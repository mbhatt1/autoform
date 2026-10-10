"""Load executable bytes without executing the input or guessing an ISA.

Relocatable objects are accepted as analysis inputs, but relocation sites remain
explicit gaps: a pre-link instruction is not the instruction a CPU will execute.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Region:
    name: str
    address: int
    data: bytes


@dataclass
class Image:
    format: str
    language: str | None
    entry: int | None
    code: list[Region]
    data: list[Region] = field(default_factory=list)
    gaps: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)


ELF_LANGUAGES = {
    ("EM_X86_64", True, 64): "x86:LE:64:default",
    ("EM_386", True, 32): "x86:LE:32:default",
    ("EM_AARCH64", True, 64): "AARCH64:LE:64:v8A",
    ("EM_AARCH64", False, 64): "AARCH64:BE:64:v8A",
    ("EM_RISCV", True, 64): "RISCV:LE:64:RV64GC",
    ("EM_RISCV", True, 32): "RISCV:LE:32:RV32GC",
}


def load_elf(path: Path) -> Image:
    from elftools.elf.elffile import ELFFile
    from elftools.elf.relocation import RelocationSection

    with path.open("rb") as stream:
        elf = ELFFile(stream)
        language = ELF_LANGUAGES.get((elf["e_machine"], elf.little_endian, elf.elfclass))
        image = Image("elf", language, int(elf["e_entry"]) or None, [])
        sections = list(elf.iter_sections())
        for section in sections:
            if section["sh_flags"] & 4 and section["sh_type"] != "SHT_NOBITS":
                image.code.append(Region(section.name, int(section["sh_addr"]), section.data()))
            if isinstance(section, RelocationSection) and section.num_relocations():
                kind = "unapplied-relocations"
                # In relocatable ELF, sh_info identifies the section being patched.
                # Data fixups make initial memory unknown, but do not change the
                # instruction bytes of a register-only function.
                target = int(section["sh_info"])
                if elf["e_type"] == "ET_REL" and 0 < target < len(sections):
                    if not sections[target]["sh_flags"] & 4:
                        kind = "unapplied-data-relocations"
                image.gaps.append(f"{kind}:{section.name}:{section.num_relocations()}")
        for segment in elf.iter_segments():
            if segment["p_type"] != "PT_LOAD":
                continue
            # Do not allocate an attacker-controlled BSS size. Zero fill is represented
            # separately as an environment obligation until a runtime loader exists.
            image.data.append(Region("PT_LOAD", int(segment["p_vaddr"]), segment.data()))
            if segment["p_memsz"] > segment["p_filesz"]:
                image.gaps.append(f"uninitialized-bss:{segment['p_vaddr']}:{segment['p_memsz'] - segment['p_filesz']}")
        if not image.code:
            # Stripped section headers do not remove executable load segments.
            image.code = [Region("PT_LOAD:X", int(s["p_vaddr"]), s.data())
                          for s in elf.iter_segments()
                          if s["p_type"] == "PT_LOAD" and s["p_flags"] & 1 and s["p_filesz"]]
        if elf["e_type"] == "ET_REL":
            image.assumptions.append("relocatable object: code uses section addresses; equivalence after linking is not proved")
            image.data = list(image.code)
            if any(s["sh_flags"] & 2 and not s["sh_flags"] & 4 and s["sh_size"] for s in sections):
                image.gaps.append("unlinked-data-section-layout")
                image.data = []
        if any(s["p_type"] in ("PT_INTERP", "PT_DYNAMIC") for s in elf.iter_segments()):
            image.gaps.append("dynamic-loader-and-external-libraries-not-modelled")
        return image


def load_macho(path: Path) -> Image:
    from macholib.MachO import MachO
    from macholib.mach_o import LC_SEGMENT, LC_SEGMENT_64, LC_MAIN

    obj = MachO(str(path))
    if len(obj.headers) != 1:
        raise ValueError("fat Mach-O has multiple ISAs; extract one slice with lipo first")
    header = obj.headers[0]
    language = {0x1000007: "x86:LE:64:default", 0x100000C: "AARCH64:LE:64:v8A",
                7: "x86:LE:32:default"}.get(header.header.cputype)
    image = Image("mach-o", language, None, [])
    raw = path.read_bytes()
    main_offset = None
    segments = []
    for cmd, info, sections in header.commands:
        if cmd.cmd == LC_MAIN:
            main_offset = int(info.entryoff)
        if cmd.cmd not in (LC_SEGMENT, LC_SEGMENT_64):
            continue
        segments.append(info)
        if info.filesize:
            image.data.append(Region("segment", int(info.vmaddr),
                                     raw[info.fileoff:info.fileoff + info.filesize]))
        if info.vmsize > info.filesize and info.initprot:
            image.gaps.append(f"uninitialized-zerofill:{info.vmaddr}:{info.vmsize - info.filesize}")
        for section in sections:
            # S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS.
            if section.flags & 0x80000400 and section.size:
                if section.offset + section.size > len(raw):
                    raise ValueError("truncated Mach-O executable section")
                name = section.sectname.rstrip(b"\0").decode("utf-8", "replace")
                image.code.append(Region(name, int(section.addr),
                                         raw[section.offset:section.offset + section.size]))
            if section.nreloc:
                kind = ("unapplied-relocations" if section.flags & 0x80000400
                        else "unapplied-data-relocations")
                image.gaps.append(f"{kind}:{section.addr}:{section.nreloc}")
    if main_offset is not None:
        for segment in segments:
            if segment.fileoff <= main_offset < segment.fileoff + segment.filesize:
                image.entry = int(segment.vmaddr + main_offset - segment.fileoff)
                break
    if header.header.filetype == 1:
        image.assumptions.append("relocatable object: code uses section addresses; equivalence after linking is not proved")
    else:
        # Loading dyld fixups/imports would be a distinct semantics layer.
        image.gaps.append("mach-o-loader-fixups-and-imports-not-modelled")
    return image


def load_pe(path: Path) -> Image:
    import pefile

    pe = pefile.PE(str(path))
    try:
        base = int(pe.OPTIONAL_HEADER.ImageBase)
        language = {0x8664: "x86:LE:64:default", 0x14C: "x86:LE:32:default",
                    0xAA64: "AARCH64:LE:64:v8A"}.get(pe.FILE_HEADER.Machine)
        image = Image("pe", language, base + pe.OPTIONAL_HEADER.AddressOfEntryPoint, [])
        for section in pe.sections:
            if section.SizeOfRawData and section.PointerToRawData + section.SizeOfRawData > path.stat().st_size:
                raise ValueError("truncated PE section")
            data = section.get_data()
            size = int(section.Misc_VirtualSize)
            if size:
                data = data[:size]
            region = Region(section.Name.rstrip(b"\0").decode("utf-8", "replace"),
                            base + section.VirtualAddress, data)
            image.data.append(region)
            if section.Characteristics & 0x20000000:
                image.code.append(region)
            if size > len(data):
                image.gaps.append(f"uninitialized-zerofill:{region.address + len(data)}:{size - len(data)}")
        if hasattr(pe, "DIRECTORY_ENTRY_IMPORT") or hasattr(pe, "DIRECTORY_ENTRY_DELAY_IMPORT"):
            image.gaps.append("external-imports-not-modelled")
        if hasattr(pe, "DIRECTORY_ENTRY_TLS"):
            image.gaps.append("tls-initialization-not-modelled")
        return image
    finally:
        pe.close()


def load_image(path: Path, fmt: str = "auto", language: str | None = None,
               base: int = 0, entry: int | None = None) -> Image:
    with path.open("rb") as stream:
        magic = stream.read(4)
    if fmt == "auto":
        if magic == b"\x7fELF":
            fmt = "elf"
        elif magic[:2] == b"MZ":
            fmt = "pe"
        elif magic in (b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf", b"\xce\xfa\xed\xfe",
                       b"\xfe\xed\xfa\xce", b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca"):
            fmt = "mach-o"
        else:
            raise ValueError("unrecognized executable format; use --format raw --language <SLEIGH-ID> for raw bytes")
    if fmt == "raw":
        if not language:
            raise ValueError("raw bytes require --language; assembly text is not machine code")
        region = Region("raw", base, path.read_bytes())
        image = Image("raw", language, base, [region], [region])
    else:
        try:
            image = {"elf": load_elf, "mach-o": load_macho, "pe": load_pe}[fmt](path)
        except ImportError:
            raise
        except Exception as exc:
            raise ValueError(f"cannot load {fmt}: {exc}") from exc
    if language and image.language and language.split(":")[:3] != image.language.split(":")[:3]:
        raise ValueError(f"--language {language} conflicts with file architecture {image.language}")
    image.language = language or image.language
    if not image.language:
        raise ValueError("architecture/mode is ambiguous; supply --language <SLEIGH-ID>")
    if entry is not None:
        image.entry = entry
    if not image.code or not any(r.data for r in image.code):
        raise ValueError("no executable bytes found")
    ranges = sorted((r.address, r.address + len(r.data)) for r in image.code if r.data)
    if any(a[1] > b[0] for a, b in zip(ranges, ranges[1:])):
        raise ValueError("overlapping executable sections; link the object or select a raw region first")
    return image

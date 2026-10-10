"""Source closure of a Joern script and its relative `using file` directives."""
from pathlib import Path
_USING_FILE = "//> using file"


def source_files(entry):
    """Return each compile unit once, in declaration order, including the entry.

    Joern resolves the unquoted directive suffix relative to the importing file.
    Missing units are errors: a partial compiler fingerprint is not evidence.
    """
    pending, seen, result = [Path(entry).absolute()], set(), []
    while pending:
        path = pending.pop()
        # A file symlink can expose the same bytes from another import base;
        # its relative directives then name different compile units.
        identity = (path.resolve(), path.parent.resolve())
        if identity in seen:
            continue
        text = path.read_text(encoding='utf-8')
        seen.add(identity)
        result.append(path)
        # Match Joern's loader: trim the line, remove the exact prefix, then
        # trim its raw suffix. Tabs/multiple spaces after `file` are accepted.
        names = [line.strip()[len(_USING_FILE):].strip()
                 for line in text.splitlines() if line.strip().startswith(_USING_FILE)]
        pending.extend(reversed([path.parent / name for name in names]))
    return result

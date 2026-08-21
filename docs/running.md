# Installing and running autoform

Written for someone who has never run this repository. Nothing below embeds a result;
where a number would be useful, the command that produces it is given instead. Figures
move with every change; where a document and an artifact disagree, the artifact wins.

---

## 1. Prerequisites

### Lean, via `elan`

The toolchain is pinned in `lean-toolchain` (Lean 4.30.0-rc1 at the time of writing).
Install `elan` and let it read the pin:

```sh
curl -sSfL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain "$(cat lean-toolchain)"
export PATH="$HOME/.elan/bin:$PATH"
lean --version && lake --version
```

`leanchecker` — the independent kernel replay used by the trust audit — **ships with the
toolchain** (v4.28.0+). There is nothing to install and no Homebrew formula; the
standalone `lean4checker` is deprecated. Verify:

```sh
lake env leanchecker --help >/dev/null && echo present
```

Then build. The first build fetches and compiles Specimen and Plausible and is slow;
subsequent builds are incremental.

```sh
lake build
```

### Joern — pinned, like the Lean toolchain

Joern supplies the code property graph that is this project's universal front end. It is a
**~1.7 GB download**, which is why CI never installs it on the gating build — the Joern
end-to-end job is opt-in.

**The version is pinned in `joern-version`, and the pin is load-bearing.** The neutral AST
is a *function of the front end*: which nodes exist, how `fullName`s resolve, whether
`IS_VARIADIC` is set, whether an absent clause is elided. Two machines running different
Joern builds produce different `ast-*.json` from identical source, and until this pin
existed nothing would have shown it. Treat it exactly as you treat `lean-toolchain`.

```sh
cat joern-version                                  # 4.0.606
python3 scripts/provenance.py joern-version --check # compares it to what is installed
```

The check reads the version out of `$JOERN_HOME/joern-cli/lib/io.joern.joern-cli-*.jar`
rather than booting `joern --version`: it is a fact about the bytes on disk, it takes
milliseconds instead of a JVM start, and it catches the "installed nothing, exited 0"
failure below, which a version banner cannot.

Changing the pin is a deliberate act that invalidates every artifact: bump it, regenerate
each `ast-*.json`, re-render each `Autoform/Generated/*.lean`, re-record provenance. §5
describes how that is checked.

**On macOS arm64, do not trust the official installer.** `joern-install.sh` can **exit 0
while having failed**, leaving no `joern-cli` directory and a shell that reports success.
Fetch the release asset directly instead:

```sh
# pick a release from https://github.com/joernio/joern/releases (4.0.606 is known-good)
curl -L -o joern-cli.zip \
  https://github.com/joernio/joern/releases/download/v4.0.606/joern-cli.zip
mkdir -p ~/joern && unzip -q joern-cli.zip -d ~/joern
~/joern/joern-cli/joern --version
```

The scripts look for `"$JOERN_HOME/joern-cli"` with `JOERN_HOME` defaulting to `~/joern`,
so the layout above needs no configuration. Joern needs a JDK (temurin 21 is what CI uses).

On Linux the official installer generally works:

```sh
curl -L https://github.com/joernio/joern/releases/latest/download/joern-install.sh -o joern-install.sh
chmod +x joern-install.sh && sudo ./joern-install.sh --without-plugins
```

Confirm the binary runs before believing the install — "exit 0" is the shape a silent
failure takes.

### The source tree the CPG was built from — a hard precondition

**The exporter needs the source tree, not only the CPG. CPG-only analysis is not
possible.** This is a new precondition and the most likely reason an otherwise-correct
invocation fails, so it is stated here rather than in troubleshooting alone.

`cartographer/export_ast.sc` reads the original source text, and the reason is `*args` /
`**kwargs`. Joern's `pysrc2cpg` sets `IS_VARIADIC` on `*args` and sets **nothing** on
`**kwargs`: by every graph property, `**kwargs` is indistinguishable from an ordinary
positional parameter. No CPG property records the stars. What the CPG does carry is
`OFFSET`, the parameter name's byte offset in its file, so the exporter opens the file at
that offset and counts the `*`s before the name.

The alternative — treating `**kwargs` as positional — is a silent mistranslation of exactly
the kind the hole mechanism exists to prevent, so the exporter **aborts** instead:

```
export_ast: cannot read source for <file> (root='<cpg.metaData.root>') to decide
whether parameter '<name>' is `*args` or `**kwargs`. Run the exporter against the tree
the CPG was built from.
```

What this means in practice:

* The tree must still be at the path recorded in `cpg.metaData.root` when the exporter
  runs. Moving or deleting a source tree after `joern-parse` breaks a later re-export.
* A `.cpg` archived on its own is **not** sufficient to regenerate an AST. Archive the
  source revision with it — which is what `provenance/<artifact>.prov.json` records (§5).
* The star-count is gated to `.py` files. In C and C++ a `*` before a parameter name is a
  pointer, not a splat.

A missing source tree fails the run loudly instead of producing a mistranslation. That is
the intended behaviour; the fix is to re-parse from the tree, or to run the exporter
somewhere that path resolves.

### Python

Python 3 is required for the transpiler's printer, the oracles and the assurance-case
emitter. **Some corpora need a specific interpreter**: the differential and execution
oracles import and run the target repository's own test suite in-process, so they must run
under a Python the corpus supports. `cachetools`' suite needs **Python 3.11**, and the
oracles say so when they detect a mismatch:

```sh
python3.11 scripts/differential.py ast-Cachetools.json ~/src/cachetools Cachetools 5
```

A C compiler (`cc`) is needed only for the C conformance corpus.

## 2. The two entry points

### `./autoform.sh <source-dir> [ModuleName]` — translate

Six stages, each announced:

| Stage | What it does | What it writes |
|---|---|---|
| `[1/6] parsing` | `joern-parse` builds the CPG | `cpg.bin` in a temp dir |
| `[2/6] cartographer` | call graph, effect classes, formalizability score | `formalization-graph.json` |
| `[3/6] transpiler` | CPG → language-neutral JSON AST; prints `exported N methods` | `ast-<Module>.json` |
| `[4/6] rendering Lean` | deterministic JSON → Lean printer | `Autoform/Generated/<Module>.lean` |
| `[5/6] type-checking` | `lake build Autoform.Generated.<Module>` | `.olean` |
| `[6/6] differential conformance` | replays the corpus's own test suite against the Lean interpreter | `conformance.json` |

then instantiates `scripts/ledger.lean.tmpl` and `#eval`s it, which prints the ledger and
writes `ledger-<Module>.json`.

Stage 6 is allowed to fail without failing the run: a divergence is a *finding*, and the
script records it and continues.

### `./assure.sh <source-dir> <ModuleName>` — translate and argue

Runs `autoform.sh`, then:

| Stage | Tool | Artefact |
|---|---|---|
| 2/5 conformance | `scripts/differential.py` | `conformance.json` |
| 3/5 axiom + escape-hatch audit | `scripts/audit_all.py` (after a full `lake build`) | `audit.json` |
| 4/5 specification teeth | `scripts/mutate.py` | `mutation.json` |
| 5/5 assurance case | `scripts/sacm.py` | `sacm-<Module>.json` |

Steps 2–4 **may legitimately fail** — a divergence, a leaked axiom or a surviving mutant
are all real findings, and the pipeline records them and continues, because a suppressed
finding is worse than a red build. Only step 5 decides whether the top claim is assertable,
and `assure.sh` exits with its status.

## 3. Reading the ledger

The human form is printed at the end of `autoform.sh`:

```
╭─ autoform trust ledger ─ <Module>
│ functions translated : …
│ AST nodes            : …
│ holes                : …  (…% of nodes)
│ hole-free (upper bd) : … / … functions
│ VERIFIABLE CORE      : … / … functions — hole-free AND call-closed
│ dynamic-hole risk    : … constructs may hole at runtime (input-dependent)
│ semantics            : Autoform.Core (fuel-indexed, total, no sorry)
│ transpiler           : Joern CPG → Core, deterministic
│ NOT PROVED           : transpiler faithfulness — see conformance.json
├─ holes by cause ─────────────────────────────────────────────
│ N  <hole label>
…
```

How to read it:

* **hole-free** is an *upper bound*: no holes in the AST. It says nothing about what the
  interpreter does with that AST.
* **VERIFIABLE CORE** = hole-free **and** call-closed (every call and method target
  resolves inside the translated program). This is the honest number, because an
  untranslated callee is invisible in the AST — a call to a function that was never
  translated looks exactly like a call to one that was.
* **dynamic-hole risk** counts constructs that *can* hole on some input. It is the static
  analysis admitting what it cannot adjudicate; only `scripts/core_oracle.py` settles it.
* **holes by cause** is the taxonomy from `docs/core-language.md`. Nothing is dropped
  silently, so this table lists everything the translation refused to guess at.
* **NOT PROVED : transpiler faithfulness** is the trust boundary, not boilerplate.

`ledger-<Module>.json` is the same data, tagged with `module` and `dialect` so that
`scripts/sacm.py` can attribute it. Untagged evidence cannot support a claim about a
subject, and the assurance case caps it accordingly.

## 4. Running individual oracles

```sh
# conformance vs the real runtime (CPython / cc)
python3.11 scripts/differential.py ast-<M>.json <src-dir> <M> 5 [--tests DIR]

# execution oracle over the claimed verifiable core
python3.11 scripts/core_oracle.py ast-<M>.json <M> <src-dir> [-n 24] [--fuel 5000]

# axioms, escape hatches, kernel replay  (--strict fails on a missing leanchecker)
python3 scripts/audit_all.py --strict

# mutation gate, hand-written Lean
python3 scripts/mutate.py Autoform/Lang/Imp/Semantics.lean Autoform.Lang.Imp.Semantics --max-mutants 8

# mutation gate, generated module (mutate the data, rebuild the specs about it)
python3 scripts/mutate.py Autoform/Generated/<M>.lean Autoform.Generated.<M> \
        --spec-file Autoform/Specs/<M>Spec.lean --spec-module Autoform.Specs.<M>Spec \
        --decls f_a,f_b

# assurance case
python3 scripts/sacm.py --module <M> [--markdown sacm-<M>.md]

# scale measurement, stage by stage (see docs/scale.md)
python3 scripts/scale_test.py --out results.json --target Name /path/to/repo
```

`Demo.lean` (`lake env lean Demo.lean`) is a guided tour of the refutation gate, the axiom
audit, vacuity detection and the ledger. It **deliberately contains an admitted theorem and
two failing audits**, so `lean` exits non-zero by design; what matters is that
`TRUSTED-CODE LEAK` and `VACUOUS` appear in the output. CI asserts exactly that.

## 5. Reproducibility and provenance

`lake-manifest.json` pins every Lean dependency and `lean-toolchain` pins the compiler, so
the Lean half of the pipeline is reproducible. `joern-version` plus the records under
`provenance/` do the same for the front-end half.

### The cheap check — run it anywhere

```sh
python3 scripts/check_provenance.py             # no Joern, no CPG, no source tree needed
python3 scripts/check_provenance.py --strict    # also refuse the unattributed backlog
python3 scripts/check_provenance.py --verify-source   # re-derive source_revision if present
```

It answers six questions from tracked bytes alone:

| Check | Fails when |
|---|---|
| coverage | an `ast-*.json` has neither a record nor a named backlog entry |
| integrity | the record's `artifact_sha256` is not the file's digest |
| pin | the record's `joern_version` differs from `joern-version` |
| **exporter** | `cartographer/export_ast.sc` changed since the artifact was exported |
| fields | a field a regeneration needs is missing or empty |
| orphans / backlog expiry | a record describes nothing, or a backlogged artifact's digest moved |

The **exporter** row is the one that matters most, because the `.cpg` files are not tracked
and never will be — they are hundreds of megabytes. A committed AST therefore cannot be
diffed against a re-export of its own CPG. But it does not need to be: the moment the
exporter changes, every AST recorded against the old exporter is *mechanically known* to be
stale, and its record carries the exact command that regenerates it.

Finding nothing to check is a failure, not a pass: with no `ast-*.json` present the script
exits 2 and says so.

### Producing an attributed artifact

```sh
scripts/export_with_provenance.sh <source-dir> <ModuleName>
```

`joern-parse` → `export_ast.sc` → `provenance.py record`, refusing to start unless the
installed Joern matches the pin. `./autoform.sh` does **not** yet record provenance (see
docs/architecture.md, "Merge-phase changes this asks for elsewhere"), so an AST it produces
is unattributed and the checker will name it.

To record provenance for an artifact produced some other way:

```sh
python3 scripts/provenance.py record \
  --artifact ast-<M>.json --source <source-dir> \
  --exporter cartographer/export_ast.sc --command '<the exact command you ran>'
python3 scripts/provenance.py show ast-<M>.json
```

`source_revision` is the source tree's git commit when it is a checkout (with `+dirty` when
it is not clean) and a `tree-sha256:<digest>:<n>files` content digest when it is not — an
unpacked tarball, for instance. Both are re-derivable from the same bytes later, which is
the only property required. `record` refuses rather than inventing a value it cannot
determine.

### The expensive check — independent recomputation

```sh
python3 scripts/reproduce_ast.py ast-<M>.json [--source <dir>] [--keep <dir>]
```

Rebuilds the CPG from the recorded source tree with the pinned Joern, re-runs the committed
exporter, and diffs. It never reads the committed AST to decide what to expect. Exit 0 =
byte-for-byte reproduction, 1 = differs (with a summary of how), 2 = could not run, with the
reason. Minutes per corpus, which is why it is a command and not a build step.

### The unattributed backlog

`provenance/unattributed.json` lists the `ast-*.json` files that predate this mechanism.
It is a **named gap, not an exemption**: every entry is printed by name on every run, and an
entry stops applying the moment its artifact's digest changes — regenerate one and you must
record real provenance for it.

Three of them were re-exported to find out rather than assumed, and **all three differ from
a fresh export** with the pinned Joern and the committed exporter: `ast-Sample.json` and
`ast-Stress.json` are missing the module-initializer entries the exporter now emits, and in
`ast-CMath.json` every integer literal is `"v": 0` where a fresh export writes `"v": "0"`.
That is recorded in the file as the finding it is. The remaining eight were not reproduced
because the source tree they came from is not identified anywhere in the repository — which
is the same gap, one step earlier.

## 6. Troubleshooting

**`leanchecker` passes but checked nothing.** Always pass `--fresh`. Without it the checker
can silently no-op on a module that has only imports and no declarations of its own —
exactly the shape of `Autoform.lean`. `scripts/audit_all.py` uses `--fresh` by default and
records which mode ran in `audit.json`; `--no-fresh` exists but is strictly weaker. If you
invoke the checker by hand, use `lake env leanchecker --fresh Autoform` (~1.5 min).

**`leanchecker` is missing.** The audit reports UNVERIFIED — never a pass — and `--strict`
turns that into a non-zero exit. A gap that is reported is a gap; a gap that is skipped
silently is a lie.

**`export_ast: cannot read source for …`.** The exporter needs the source tree the CPG was
built from, at the path recorded in the CPG metadata — see §1, "The source tree the CPG was
built from". It is deciding whether a parameter is `*args` or `**kwargs`, which no CPG
property records. Re-parse from the tree, or run the exporter where that path resolves.
The failure is deliberate: without the source text the exporter would have to guess, and a
guess here is a mistranslation rather than a hole. If all you have is a `.cpg`, you cannot
export from it; you need the source revision, which is why `provenance/` records it.

**`joern-version: MISMATCH`.** The installed Joern is not the pinned one. Do not just
proceed: the neutral AST is a function of the front end, so anything you regenerate will
differ from its neighbours for reasons that have nothing to do with the source. Install the
pinned release (§1) or change the pin deliberately and regenerate everything.

**`check_provenance: … changed since this artifact was exported`.** The exporter moved and
the committed ASTs did not. This is the check working. Regenerate the artifact with the
command in its record (`scripts/provenance.py show ast-<M>.json`), re-render the Lean module
from it, and re-record. Do not edit the record to match the new exporter digest — that
turns a real staleness finding into a green check.

**`check_provenance: found no ast-*.json … Nothing was checked`.** Exit 2, not 0. You are
running it somewhere without the artifacts; pass `--root`.

**The oracle reports divergences that make no sense.** Suspect a stale `.olean` first. An
oracle reading a stale cache answers with the *previous* semantics and produces confident,
specific, wrong findings. `differential.py` and `core_oracle.py` both `lake build` before
comparing; if you are running something by hand, build first.

**The audit reports failures unrelated to soundness.** It sweeps every declaration in the
built library, so the **whole** library must be built first. `autoform.sh` only builds the
generated module; run a bare `lake build` before `audit_all.py` (this is why `assure.sh`
does).

**Joern "installed" but nothing works.** See §1 — the macOS arm64 installer exits 0 on
failure. Check that `$JOERN_HOME/joern-cli/joern-parse` exists and runs.

**The differential harness finds zero comparable cases.** Usually one of: (a) the test
suite was not found — discovery walks up from the source root, and a `src/`-layout repo
with sibling `tests/` needs the repo root, not `src/`; (b) the interpreter is wrong for the
corpus (try `python3.11`); (c) the arguments are unencodable (floats, sets, locks, very
wide containers) or the receivers are `tuple`/`dict` subclasses, which Core cannot
represent as objects. Cases refused for (c) are counted under `unencodable_reasons` in
`conformance.json` — refused, never silently compared.

**A mutation run reports a suspiciously round score.** If a mutant makes the module fail to
compile, every theorem in that module is credited with killing it. The aggregate is sound;
per-theorem attribution is coarse.

**Build is slow.** Specimen and Plausible dominate. Cache `.lake` (CI keys the cache on
`lean-toolchain`, `lake-manifest.json`, `lakefile.toml` and the source hashes).

**`Autoform/Generated/*.lean` looks wrong.** Do not hand-edit it. It is a pure function of
`ast-<Module>.json`; re-run `cartographer/render_lean.py`, and if the AST is wrong, fix the
exporter.

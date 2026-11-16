# Repository analysis

Run a repository with one command:

```sh
autoform https://github.com/OWNER/REPOSITORY.git
```

The CLI pins the checkout revision, inventories the selected directory, and chooses
the available source adapters from the files actually present. Python, C/C++, Java,
Go, JavaScript, TypeScript and Kotlin have adapters for specific extensions. Adapter
availability does not establish complete language semantics. Scala and other
unimplemented source languages remain explicit gaps. No language is silently
substituted for another one.

Each language job uses the original checkout for imports, headers, tests and build
context. Files are not copied into a reduced source tree. Jobs run sequentially in
one workspace because proof builds and mutation restoration share state. Concurrent
installed CLI commands need separate workspaces; a workspace lock rejects overlap
before prior evidence is changed.

When a supported language is present, the workflow attempts native comparison and
proof generation for its represented functions. One failed language job does not
prevent later language jobs. Unsupported-only and empty source trees still produce
an inventory and an unverified report. Checkout/network failures are reported before
analysis and do not masquerade as an empty source tree.

The report directory is `.autoform-work/artifacts/pipeline/Translated` by default.
Single-language results retain the existing report paths.
Unsupported languages count toward the routing decision: a Python-and-Scala
repository receives a parent report and a Python child, with Scala's files and
requirements retained as unresolved.

Mixed-language runs add child modules such as `TranslatedJava` and
`TranslatedPython`, linked from the parent:

- `inventory.json`: every discovered file, content hashes, language classification,
  unsupported extensions, special files, scan errors and explicit exclusions.
- `source-coverage.json`: which inventoried files have an exported AST entry,
  which are absent or unsupported, and changes observed after execution.
- `repository-summary.json`: child results, exact property routing and remaining gaps
  for a mixed-language or unsupported-only run.
- `guarantee.json`: the exact status and evidence references. A repository report
  retains child certificates without promoting their claims to whole-repository proof.

The inventory hashes regular files without following symlinks or reading special
files. VCS metadata and the active output workspace are explicitly excluded, and so
are the Gradle/Maven build products and test sources described below. File
presence in an AST does not show that every function parsed successfully. Export
truncation and the lack of an independent compiler function census remain visible.
Files outside the selected directory, including external dependencies, are outside
the inventory. Native execution runs in the worker sandbox (no network, writes only
under its work directory; `native-build.json` records the mechanism), which is not a
container and limits no CPU or memory.

### Gradle and Maven projects

A directory holding `settings.gradle[.kts]`, `build.gradle[.kts]` or `pom.xml` makes
its subtree a JVM build tree. Inside one, the inventory excludes, each under
`excluded` with its reason: `.gradle/` and any `build/` or `target/` outside `src/`
(`build_output`); `generated/`, `generated-src/` and `generated-sources/`
(`generated_code`); and test source sets such as `src/test`, `src/testFixtures` and
`src/integrationTest` (`test_source_set`). The frontend still parses the whole tree,
so the functions it exported from those paths are dropped from the model under the
same reasons and listed in `selection.json`; `autoform source` does the same when the
analysed directory is a Gradle/Maven root. `inventory.json`'s `layout` names the
build systems, the directories holding a build file, and the remaining
`src/<set>/{java,kotlin}` source roots, so a multi-module project needs no `--subdir`.
To model a test source set itself, select it with `--subdir`, below the build file.
The Java oracle samples static methods with random inputs; it does not run the
project's JUnit tests. `tests/test_repository_layout.py` pins all of this on the
multi-module fixture in `tests/fixtures/jvm_multimodule/`.

Requirements in `autoform.properties.json` or `--properties` are frozen before source
execution. Mixed-language routing requires each exact subject to appear in a fresh
child model. Unmatched or ambiguous requirements remain unresolved; a claim is never
dropped merely because its language is unsupported. Source/configuration changes or
changes to an earlier child's evidence invalidate its eligibility for the current
repository result.

The overall command returns `1` when gaps remain. Child `verified_scoped` results
describe their recorded inputs or supplied propositions. Full source equivalence,
behavior across language boundaries and absence of arbitrary bugs remain unproved.
The lower-level `autoform source` / `autoform.sh` entry point still performs one source
translation; use the URL or `autoform assure` workflow for repository-wide dispatch.

# Third-party material

The CLI wheel and its source distribution include
`Autoform/Generated/Cachetools.lean`, a generated Lean translation of
[cachetools](https://github.com/tkem/cachetools), used by the contracts examples.
The repository's corpus workflow pins upstream revision
`01af8e5b7ce44432b357e26c7d67eb7fa055ae72` (abbreviated `01af8e5`).
The translation changes the implementation language and contains explicitly
untranslated operations; it is not an upstream cachetools release.
Copyright and MIT permission terms are preserved in
[licenses/cachetools-MIT.txt](licenses/cachetools-MIT.txt), which matches the
[notice at the pinned revision](https://raw.githubusercontent.com/tkem/cachetools/01af8e5b7ce44432b357e26c7d67eb7fa055ae72/LICENSE)
byte for byte. The required repository CI also compares its complete notice with
the pinned upstream file and blocks release on a difference or unavailable input.

The Python package installs Hypothesis separately. The optional `machine` extra
installs pypcode, pyelftools, macholib and pefile separately. Their dependencies
and license files belong to their own distributions; they are not vendored in
Autoform's runtime archive. `pyproject.toml` records the requested versions.

Lean, Joern, Git, compilers and source runtimes are external tools. Lake downloads
specimen, aesop, batteries, plausible and proofwidgets at the revisions in
`lake-manifest.json`. They are not copied into the CLI archive. A distributor
who bundles these tools or dependencies must also preserve their notices.

The development repository also contains historical translations and evidence
from other projects, including Linux and V8. They are excluded from the CLI
runtime bundle and are not relicensed by Autoform's Apache license. This file
inventories the CLI distribution; it is not a completed license review of every
historical corpus or of a customer's analyzed repository. Preserve original
repository license obligations when distributing source or translated models.

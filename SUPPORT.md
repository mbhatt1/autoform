# Support

Autoform is an open-source CLI with paid engineering support. The CLI's source
and proof features are available under the licenses in [NOTICE](NOTICE).
Paying for support does not change a theorem's assumptions, convert an open
obligation into a proof, or extend a guarantee to unexamined code.

Community bug reports and feature requests belong in the
[issue tracker](https://github.com/mbhatt1/autoform/issues). Include the CLI
version, operating system, toolchain versions, exact command, selected source
revision and a small reproducer. Attach redacted `summary.md`, `run.json` and
the failing stage log. Review artifacts before sharing: they can contain source,
paths and application data. Follow [SECURITY.md](SECURITY.md) for security bugs.

Paid engagements can cover installation and CI integration, defining security
properties, reproducing translation disagreements, and extending supported
semantics with native comparisons and kernel-checked regression proofs. Open a
non-sensitive support inquiry in the issue tracker to request an engagement.
Share confidential code only through a channel agreed with the provider.

Each engagement must state the supported package and toolchain versions, target
languages and architectures, repository scope, deliverables, response times,
fees, confidentiality terms and duration in a separate written agreement.
This repository does not promise an SLA, emergency response, certification,
indemnity or universal absence of vulnerabilities.

The current package is an alpha. macOS and Linux are the package CI targets;
source language coverage and machine-code limitations are documented in
[docs/packaging.md](docs/packaging.md) and
[docs/machine-code.md](docs/machine-code.md). Install the Lean and Joern
versions named in the package's `lean-toolchain` and `joern-version` files;
those external tools are not bundled. Create a fresh workspace after upgrades.
Report formats can change before 1.0; consume their explicit schema versions
where provided, and fail closed on unknown versions or missing required evidence.

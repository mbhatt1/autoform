# Assurance run: CompilerRewrite

Execution: **completed_with_gaps**. Verification complete: **false**.

Compared cases: 15; divergences: 0; translation holes: 0.

Conformance specifications: 3 proved; 0 open obligations.

Source files represented in the model: 1; supported files absent from it: 0; unsupported files: 0.

File presence does not prove complete parsing or translation. [All files and source stability](source-coverage.json).

| Stage | Status | Detail |
|---|---|---|
| source | completed | exit 0; [log](source.log) |
| core-oracle | completed | exit 0; [log](core-oracle.log) |
| mutation | completed | exit 0; [log](mutation.log) |
| restore-build | completed | exit 0; [log](restore-build.log) |
| audit | completed | exit 0; [log](audit.log) |
| contracts | completed | exit 0; [log](contracts.log) |
| assurance | completed | exit 1; [log](assurance.log) |

A completed workflow is not a proof of the entire codebase. Unsupported, unexercised and failed checks remain gaps.

[Proof guarantee and scope](guarantee.md) · [Detailed assurance argument](assurance.md) · [Machine-readable stage report](run.json)

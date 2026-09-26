# Using Autoform for security

Autoform can provide evidence about security-critical code when the security
requirement is stated independently of the implementation. The most practical
first target is a small validation or authorization function and a specific
vulnerability fix. The automatic pipeline establishes native conformance on recorded
cases. With a property manifest, it also attempts independently supplied Lean propositions,
including quantified properties. It does not infer the intended security policy.

An implementation and its generated model can agree while both violate a security
requirement. A successful `conform_*` theorem therefore must not become an
"absence of vulnerabilities" claim. `scripts/guarantee.py` records the finite
case scope and explicitly excludes that claim.

| Security application | Example requirement | Work needed beyond the current automatic pipeline |
|---|---|---|
| Validate a vulnerability fix | The reported attack input is rejected; the documented valid inputs still succeed. | Import the generated model into an independent security specification; compare vulnerable and patched revisions. |
| Verify an authorization decision | A successful decision implies ownership or an explicitly permitted role. | Supply the policy and model the relevant identity and state; a local predicate alone does not establish endpoint enforcement. |
| Check length and arithmetic guards | An accepted allocation request cannot overflow its target integer width. | Specify the target ABI, input domain and overflow property; prove the selected domain or report it as open. |
| Check parser validation | A claimed input length cannot exceed the available input before a read. | Supply buffer/lifetime semantics and a parser harness; current memory coverage is incomplete. |
| Prevent security regressions | Removing or weakening the repaired guard fails its security specification. | Add security-specific mutations and run the property against subsequent changes. |

## Run the evidence pipeline today

From an installed environment, with Git, Lean, Joern and the target runtime available:

```sh
autoform --workspace ./proofs https://github.com/OWNER/REPOSITORY.git \
  Review --ref COMMIT --subdir path/to/component
```

The URL workflow pins a checkout, translates it, compares supported native cases,
generates conformance proofs, checks mutations, replays proofs independently and
publishes the evidence. Inspect `proofs/artifacts/pipeline/Review/guarantee.json`
for the exact claims and `summary.md` for failed or unsupported stages. A nonzero
assurance result can mean the workflow completed with explicit gaps.

Each assurance stage has a finite deadline, defaulting to 7200 seconds. Set
`--stage-timeout SECONDS` on the Git URL command or `assure.sh` to change it.
A timeout records `timed_out` and exit 124 in `run.json`, preserves the stage log,
and withholds its verification. On timeout or interruption, the driver sends an
interrupt and allows up to two seconds for cleanup before killing the process group.
Mutation cleanup restores the source and terminates its compiler session without
starting a new build while cancellation is in progress; later verification must rebuild.
Remaining descendants in the stage's group are also killed after parent completion.
This does not contain processes that create new sessions and does not provide a
filesystem or network sandbox.

## Supply an independent property

The included ownership predicate and its independent requirement run in one command:

```sh
./assure.sh examples/security SecurityPolicy
```

The driver discovers `autoform.properties.json` at the root of the selected source
directory, including a Git checkout. With `--subdir path/to/component`, put the
manifest in that component. It does not search parent directories. An explicit
`--properties /path/to/properties.json` overrides discovery; explicit paths are
relative to the caller and may be outside the repository. Requirements are copied
before executing source code, and their selection and hash are recorded in `run.json`.
Invalid or unreadable manifests withhold the security guarantee; an automatic
manifest symlink must stay inside the selected source directory.

Review the manifest independently of the implementation. A repository can supply
an incomplete or weak policy; discovering it cannot establish that it represents
your security requirements. Use an independently maintained override when needed.

The input format is:

```json
{
  "schema_version": 1,
  "claims": [{
    "id": "owner_only",
    "subject": "policy.py:<module>.authorize",
    "statement": "∀ owner caller : Int, runFunc program 32 \"policy.py:<module>.authorize\" [.int owner, .int caller] = .val (.bool (owner == caller))"
  }]
}
```

`subject` is the exact exported function name from `ast-<Module>.json`. `statement`
is a Lean proposition, with `Autoform.Core` and the generated model's namespace open.
Every variable and premise must be explicit. An optional `description` explains the
requirement; it is not a substitute for the formal statement. An optional `proof`
contains a Lean proof term such as `by intro owner caller; rfl`. Otherwise the tool
introduces quantified variables and tries kernel computation and the proof portfolio.
Unknown fields, duplicate IDs, ambiguous subjects and incomplete term syntax are rejected.

Each proof must depend on its named subject and use only permitted Lean axioms.
Failed attempts are recorded in `security-claims.json` as unresolved obligations;
they never become admitted theorems or native-confirmed vulnerabilities. Successful
claims are emitted into `Autoform/Security/<Module>.lean`, tested against mutations
of their subjects, restored, and independently replayed. `security.json` and
`security.md` report their exact scope. Single-language jobs with a property manifest
receive a schema-version-3 `guarantee.json` with a separate `security` section.
Mixed-language repositories receive a schema-version-4 parent report linking child
certificates and recording each property's routing status. Unsupported languages
count toward mixed-language routing even when only one adapter can run. If any
requested property or its evidence is unverified, the overall guarantee is withheld.
Native property validation is explicitly `not_run`: this interface does not yet
translate arbitrary Lean propositions into executable native counterexample searches.

The example quantifies over all integer IDs in the model. It does not establish
that a deployed endpoint obtains trustworthy IDs, calls this predicate, or implements
the generated model faithfully for every input. Those need their own evidence.
Statements can also specify finite cases; quantification comes from the proposition,
not from a badge or a case count. Property files contain executable Lean proof code
and require the same containment as other untrusted build inputs.

The guarantee is bound to the proof source, compiled imports and pipeline evidence
observed by the audit. Changed or missing artifacts, absent theorem names, mutation
timeouts and unattributed build failures withhold the guarantee. This protects against
stale evidence under a trusted runner; report hashes do not authenticate an untrusted
runner or replace independently replaying a received proof bundle.

The native adapters execute repository code. C library loading, initializers and
function calls run in separate workers, with a three-second deadline enforced by
the parent. A timed-out worker and descendants in its process group are killed;
crashes, timeouts, load errors and missing results remain distinct report outcomes.
These workers are not a filesystem or network sandbox. Use a disposable, restricted
environment for an untrusted repository. An automated security service still needs
containment around acquisition, builds and execution.

## A concrete security-fix workflow

1. Select the source revision, build configuration, callable entry point and
   security requirement. For example: if an unsigned allocation guard accepts
   `count` and `size`, then `count = 0` or `size <= MAX / count`.
2. Collect an attack reproducer and ordinary boundary cases. Run each against the
   real vulnerable and patched implementations, preserving crashes and timeouts
   as distinct outcomes. C scalar plans reserve their first case for all-zero
   arguments, covering a zero/equality boundary; every other remaining case draws
   each argument from its ABI type's width boundaries (powers of two straddling
   32 and 64 bits and the type's extremes, where a multiply overflows), and the
   rest use seeded random inputs. This does not cover every boundary; the
   conformance generators are not a general fuzzer.
3. Translate the relevant code and inspect the holes and dependencies. A path
   reaching a hole, unknown external call or exhausted fuel remains unverified.
4. Supply an independent property in `autoform.properties.json` or with `--properties`, or write a larger hand-authored
   specification under `Autoform/Specs/` importing the generated model. Do not derive
   its expected answer from the vulnerable implementation.
   A theorem over listed inputs establishes those cases. A universal claim needs
   a theorem quantifying over its input domain, with explicit preconditions.
5. Confirm that the vulnerable revision violates the property, the patch satisfies
   the claimed scope, and a mutation that removes the repaired guard is detected.
   A proof failure by itself is not a vulnerability finding: reproduce the
   counterexample on the actual target before making that claim.
6. Audit and independently replay the security theorem, then record its statement,
   commit, target, assumptions, tested inputs and remaining gaps. The `--properties`
   workflow automates this for its supplied claims; arbitrary hand-authored modules
   are not automatically imported into the guarantee.

For native memory bugs, a future integration can feed coverage-guided
[libFuzzer](https://llvm.org/docs/LibFuzzer.html) cases and
[AddressSanitizer](https://clang.llvm.org/docs/AddressSanitizer.html) reports into
this workflow. Those tools exercise native code; their findings are test evidence,
and do not automatically become proofs of memory safety.

## What needs to be built

Remaining security-specific additions include a broader set of independent property
templates, sandboxed runtime workers, reproducible native counterexamples,
security-specific mutations, and reports that distinguish a proven property,
a native-confirmed violation, an unresolved obligation and unsupported behavior.
Quantified proof automation remains incomplete even though the input supports it.
C memory lifetime and aliasing,
concurrency, kernel execution context and source-to-model fidelity remain separate
limitations even after a property is proved in Lean.

Python functions with defaults, positional-only parameters or keyword-only parameters
currently produce explicit translation gaps. Defaults also block function creation,
because their expressions execute at definition time and may retain mutable state.
Missing required arguments to otherwise ordinary functions remain a known Core binding
limitation. Review the exact signature and modeled call domain before relying on a
property; source-language calling conventions are part of the security claim.

The recorded [Linux experiment](../artifacts/linux-fix/REPORT.md) exercised portable
helpers on the host, not a configured kernel. It confirmed no Linux vulnerability.
Its scoped conformance proofs are evidence that the pipeline can produce and
replay claims; they do not establish Linux security.

See [the trust model](trust-model.md) for the proof boundaries and
[language coverage](languages.md) for source-specific limitations.

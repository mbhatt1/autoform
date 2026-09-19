# Security reports and execution boundary

A proof accepted for the wrong source, incorrect translation reported as
agreement, stale evidence accepted as current, or an unsupported operation
reported as verified is a security-relevant Autoform bug.

Use the repository's private vulnerability-reporting facility if available,
or the private channel in your support agreement. If neither is available,
open a public issue requesting a private contact without including exploit
details, credentials or confidential source. No private contact address or
response SLA is currently published by this project.

Include the affected CLI version, source revision, command, minimal reproducer,
expected and observed behavior, and relevant evidence hashes. A maintainer
should reproduce the issue, identify affected claims, add a native regression,
replay the corrected proofs independently, and document whether prior evidence
must be regenerated. Until resolved, treat affected guarantees as unverified.

Autoform executes analyzed code, compiler tools and proof elaboration. Its
process deadlines do not provide filesystem or network isolation. Analyze
untrusted repositories in a disposable environment with no credentials and
restricted access to other systems. Evidence hashes assume a trusted runner;
they do not authenticate evidence against a malicious runner.

The alpha has no published long-term maintenance window. Supported versions
and remediation timelines for a paid engagement must be stated separately.

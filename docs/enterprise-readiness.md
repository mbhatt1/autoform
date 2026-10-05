# Enterprise readiness

Autoform now has a stable Python CLI for repeatable local and CI execution. The CLI is the supported entry point for new automation; `autoform.sh` and `assure.sh` remain compatibility wrappers that delegate to it.

## What is ready

- `autoform doctor`, `translate`, `assure`, `plan`, `batch`, `validate`, `gate`, `bundle`, `report`, `index`, `check`, `render`, and `audit` are exposed through one command surface.
- Non-dry-run `translate` and `assure` runs produce `.autoform-runs/<run-id>/run.json` manifests with planned commands, return codes, artifact paths, and audit metadata for config, repo revision, Python, Lake, Joern, and C/C++ define presence.
- `autoform gate` evaluates a single run manifest or a fleet manifest index as a CI release gate.
- `autoform bundle` packages a manifest and listed artifacts for upload.
- `autoform report` writes Markdown evidence reports for one run or an entire fleet index.
- `autoform index` summarizes many run manifests into one JSON artifact for fleet dashboards.
- `autoform check --junit --sarif` emits CI-native test XML and code-scanning JSON for render, docs, and provenance checks.
- `autoform plan`, `autoform verify-plan`, `autoform validate` and `autoform schema` provide reviewable and executable fleet contracts, including owner/tier/tag metadata used for staged rollouts.

## Current validation status

These checks pass in this checkout:

```sh
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m pytest tests/ -q
make cli-smoke
make report-smoke
python3 scripts/check_render.py
```

The remaining red checks are inherited evidence gaps, not hidden by the CLI rewrite:

- `python3 scripts/check_docs.py` fails because `ledger-Cachetools.json` is absent. That file must be regenerated with the Lean toolchain before documentation figures can be cross-checked.
- `python3 scripts/check_provenance.py` fails for four remote AST artifacts: `ast-Cachetools.json`, `ast-LangGo.json`, `ast-LangJS.json`, and `ast-LangTS.json`. Their recorded exporter hash no longer matches the committed exporter, and fresh exports attempted from recorded remote sources were not byte-identical. Do not update those provenance sidecars unless the regenerated artifact bytes match or the ASTs are intentionally replaced and downstream renders/specs are regenerated.

## Release checklist

Before treating the repository as release-clean, a maintainer should:

1. Install the pinned Lean/Lake toolchain and regenerate `ledger-Cachetools.json` from `scripts/ledger.lean.tmpl`.
2. Run `python3 scripts/check_docs.py` and update only figures that are backed by the regenerated ledger.
3. Reproduce or intentionally refresh the four failing remote AST corpora, then re-render downstream artifacts and update provenance with `scripts/provenance.py record`.
4. Run `autoform check --junit autoform-checks.xml --sarif autoform.sarif` and require zero failures in CI.
5. Upload the run manifest, Markdown report, fleet index, and evidence bundle as CI artifacts.

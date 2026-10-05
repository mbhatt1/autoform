.PHONY: help test test-local doctor cli-smoke bundle-smoke report-smoke index-smoke plan-smoke

help:
	@echo "Targets:"
	@echo "  make doctor     # check local Autoform toolchain dependencies"
	@echo "  make cli-smoke  # exercise CLI help and dry-run paths"
	@echo "  make bundle-smoke # exercise manifest artifact packaging"
	@echo "  make report-smoke # write a Markdown report from a smoke manifest"
	@echo "  make index-smoke  # write a JSON index from smoke manifests"
	@echo "  make plan-smoke   # write a JSON fleet plan from config"
	@echo "  make test       # run Python tests with ambient pytest plugins disabled"

doctor:
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(PWD) doctor || true

cli-smoke:
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(PWD) --help >/dev/null
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(PWD) --dry-run translate /tmp/sample Sample >/dev/null

test test-local:
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m pytest tests/ -q


bundle-smoke:
	python3 -c 'import json; from pathlib import Path; Path("/tmp/autoform-bundle-artifact.txt").write_text("evidence"); Path("/tmp/autoform-bundle-run.json").write_text(json.dumps({"kind":"translate","module":"Smoke","source":"/tmp/sample","run_id":"smoke","dry_run":False,"returncode":0,"artifacts":["/tmp/autoform-bundle-artifact.txt"],"steps":[]}))'
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(PWD) --json bundle --manifest /tmp/autoform-bundle-run.json --output /tmp/autoform-bundle.tar.gz >/dev/null

report-smoke: bundle-smoke
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(CURDIR) --json report --manifest /tmp/autoform-bundle-run.json --output /tmp/autoform-report-smoke.md

index-smoke: bundle-smoke
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(CURDIR) --json index /tmp/autoform-bundle-run.json --output /tmp/autoform-index-smoke.json

plan-smoke:
	python3 -c 'from pathlib import Path; Path("/tmp/autoform-plan-smoke.toml").write_text("[targets.smoke]\nsource = \"/tmp/sample\"\nmodule = \"Smoke\"\nmode = \"translate\"\ntags = [\"smoke\"]\n")'
	PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m autoform_cli --repo-root $(CURDIR) --config /tmp/autoform-plan-smoke.toml --json --run-id smoke plan --tag smoke --output /tmp/autoform-plan-smoke.json

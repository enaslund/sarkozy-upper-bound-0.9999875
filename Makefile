PYTHON ?= python3
LAKE ?= lake

.PHONY: help check paper lean-check manifest

help:
	@echo 'check       Validate release files, hashes, imports, archives and privacy checks'
	@echo 'paper       Build the PDF and independently compile the TeX upload archive'
	@echo 'lean-check  Build the Lean companion and audit all Sarkozy declarations'
	@echo 'manifest    Refresh the release inventory after intentional changes'

check:
	$(PYTHON) -B scripts/check_release.py

paper:
	$(PYTHON) -B paper/package_publication.py

lean-check:
	cd lean && $(LAKE) build Sarkozy
	cd lean && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true Audit.lean

manifest:
	$(PYTHON) -B scripts/check_release.py --write-manifest

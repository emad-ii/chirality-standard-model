PYTHON ?= python3
NOTEBOOK_PYTHON ?= $(if $(wildcard .venv/bin/python),.venv/bin/python,$(PYTHON))
NOTEBOOK_REF ?= $(if $(NOTEBOOK_RELEASE_TAG),refs/tags/$(NOTEBOOK_RELEASE_TAG),HEAD)
LATEXMK ?= latexmk
PDFINFO ?= pdfinfo
PDFTOTEXT ?= pdftotext
PDFTOPPM ?= pdftoppm
PDFFONTS ?= pdffonts
PDFDETACH ?= pdfdetach
JOBS ?= 2
PAPER_OUTDIR ?= build
PAPER_REPEAT_OUTDIR ?= ../build/paper-repeat
# 2026-09-04T05:35:03Z, the recorded manuscript release build time.
PAPER_SOURCE_DATE_EPOCH ?= 1788500103

.PHONY: all verify verify-optimized release-workflow-check lean notebook notebook-setup notebook-source-check paper paper-release-check regenerate formal-data-check formal-hygiene

all: release-workflow-check verify verify-optimized lean notebook paper-release-check

release-workflow-check:
	$(PYTHON) verification/release/check_release_workflow.py --self-test
	PYTHONOPTIMIZE=1 PYTHONDONTWRITEBYTECODE=1 $(PYTHON) verification/release/check_release_workflow.py --self-test

verify:
	$(PYTHON) verification/python/run_all.py --jobs $(JOBS)

verify-optimized:
	PYTHONOPTIMIZE=1 PYTHONDONTWRITEBYTECODE=1 $(PYTHON) verification/python/run_all.py --jobs $(JOBS)

formal-data-check:
	$(PYTHON) formal/scripts/check_generated_data.py

formal-hygiene:
	$(PYTHON) formal/scripts/check_formal_hygiene.py

lean: formal-data-check
	lake build
	$(PYTHON) formal/scripts/check_formal_hygiene.py

notebook-source-check:
	$(NOTEBOOK_PYTHON) notebooks/check_notebook_freshness.py --self-test
	PYTHONOPTIMIZE=1 $(NOTEBOOK_PYTHON) notebooks/check_notebook_freshness.py --self-test
	$(NOTEBOOK_PYTHON) notebooks/check_notebook_freshness.py --source-only --notebook Cubic_Anomaly_Master_Verification.ipynb

notebook-setup:
	test -x .venv/bin/python || $(PYTHON) -m venv .venv
	.venv/bin/python -m pip install -r requirements-notebook.txt

notebook: notebook-source-check
	set -eu; \
	expected_commit="$$(git rev-parse --verify --end-of-options '$(NOTEBOOK_REF)^{commit}')"; \
	mkdir -p build/notebook; \
	EXPECTED_COMMIT_SHA="$$expected_commit" $(NOTEBOOK_PYTHON) -m jupyter nbconvert --execute --to notebook --output Cubic_Anomaly_Master_Verification.executed --output-dir build/notebook --ExecutePreprocessor.timeout=1200 Cubic_Anomaly_Master_Verification.ipynb; \
	$(NOTEBOOK_PYTHON) notebooks/check_notebook_freshness.py --notebook build/notebook/Cubic_Anomaly_Master_Verification.executed.ipynb --require-verified-provenance --expected-commit-sha "$$expected_commit"

paper:
	SOURCE_DATE_EPOCH=$(PAPER_SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 $(LATEXMK) -norc -cd -g -pdf -usepretex='\pdftrailerid{}' -interaction=nonstopmode -halt-on-error -outdir=$(PAPER_OUTDIR) paper/paper.tex
	test -s paper/$(PAPER_OUTDIR)/paper.pdf

paper-release-check: paper
	mkdir -p build/paper-repeat
	$(MAKE) paper PAPER_OUTDIR=$(PAPER_REPEAT_OUTDIR)
	cmp -s paper/$(PAPER_OUTDIR)/paper.pdf paper/$(PAPER_REPEAT_OUTDIR)/paper.pdf
	test -s paper/$(PAPER_OUTDIR)/paper.log
	test -s paper/$(PAPER_REPEAT_OUTDIR)/paper.log
	! grep -Eq 'LaTeX Warning|Package .* Warning|Overfull|Underfull' paper/$(PAPER_OUTDIR)/paper.log paper/$(PAPER_REPEAT_OUTDIR)/paper.log
	test "$$($(PDFINFO) paper/$(PAPER_OUTDIR)/paper.pdf | awk '/^Pages:/ {print $$2}')" -eq 35
	test "$$($(PDFINFO) paper/$(PAPER_OUTDIR)/paper.pdf | awk '/^Pages:/ {print $$2}')" = "$$($(PDFINFO) paper/paper.pdf | awk '/^Pages:/ {print $$2}')"
	$(PYTHON) verification/python/check_pdf_equivalence.py --self-test
	PYTHONOPTIMIZE=1 $(PYTHON) verification/python/check_pdf_equivalence.py --self-test
	$(PYTHON) verification/python/check_pdf_equivalence.py --pdftotext $(PDFTOTEXT) --pdftoppm $(PDFTOPPM) --pdfinfo $(PDFINFO) --pdffonts $(PDFFONTS) --pdfdetach $(PDFDETACH) paper/$(PAPER_OUTDIR)/paper.pdf paper/paper.pdf

regenerate:
	$(PYTHON) verification/python/regenerate.py

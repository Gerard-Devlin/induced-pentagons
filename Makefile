PYTHON ?= python3
LABEL ?= submission_20261027

.PHONY: paper submission flatten manuscript-check finite profiles offsets inputs certificate spans verify lean lean-paper audit release all clean
# A recipe fixes ordering even with make -j: the verdict binds the final PDFs
# and flattened text, so these must be produced before the exact full check.
all:
	$(PYTHON) scripts/build_paper.py --edition both
	$(PYTHON) scripts/flatten_latex.py
	$(PYTHON) src/verify_manuscript_build.py
	$(PYTHON) src/check_manuscript_inventory.py
	$(PYTHON) src/verify_project.py
paper:
	$(PYTHON) scripts/build_paper.py --edition main
submission:
	$(PYTHON) scripts/build_paper.py --edition submission
flatten:
	$(PYTHON) scripts/flatten_latex.py
manuscript-check:
	$(PYTHON) src/verify_manuscript_build.py
finite:
	$(PYTHON) -S src/verify_finite.py --out certificates/finite_checks.json
profiles:
	$(PYTHON) -S src/verify_profiles.py --out certificates/profile_checks.json
offsets:
	$(PYTHON) -S src/verify_offsets.py --out certificates/eventual_polynomials_small_offsets.json
inputs:
	$(PYTHON) src/verify_combinatorial_inputs.py
certificate:
	$(PYTHON) src/rationalize_certificate.py --verify-only
spans:
	$(PYTHON) src/generate_equality_spans.py --verify-only
verify:
	$(PYTHON) src/verify_project.py
lean:
	$(PYTHON) scripts/verify_lean.py
lean-paper:
	$(PYTHON) scripts/verify_lean_paper.py
audit:
	$(PYTHON) -S src/verify_foundation_identities.py
	$(PYTHON) -S src/verify_stability_inputs.py
	$(PYTHON) -S src/verify_offset_polynomials.py
	$(PYTHON) src/audit_equality_spans.py
	$(PYTHON) src/verify_rejection_cases.py
release:
	$(MAKE) all PYTHON="$(PYTHON)"
	$(MAKE) audit PYTHON="$(PYTHON)"
	$(PYTHON) scripts/package_checkpoint.py --label "$(LABEL)" --require-verified
clean:
	cd manuscript && latexmk -c main.tex

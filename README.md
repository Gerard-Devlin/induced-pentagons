# Induced pentagons

[![Exact verification](https://github.com/Gerard-Devlin/induced-pentagons/actions/workflows/verify.yml/badge.svg)](https://github.com/Gerard-Devlin/induced-pentagons/actions/workflows/verify.yml)

Research materials for **Sharp bounds, stability, and arithmetic fluctuations
for induced pentagons**. The paper studies the sharp inequality

```text
I5(G) <= 3 / (50 sqrt(10)) * m^(5/2),
```

its Clebsch equality construction, stability, and finite-edge arithmetic.

**Verification scope:** the programs check exact finite certificates and
computational inputs. The graphon, compactness, stability and eventual
extremality arguments are mathematical proofs in the paper. This repository
does not contain a Lean, Isabelle or HOL formalization.

## Read the proof

- [Paper PDF](paper/submission.pdf) and [LaTeX source](paper/submission.tex)
- [Proof blueprint](blueprint/README.md): stages and dependencies
- [Claims and certificates](blueprint/claims.md): evidence for each result
- [Trust boundary](blueprint/trust.md): what a verification PASS establishes

## Verify

From the repository root, in an activated Python environment:

```sh
python -m pip install -r requirements-verification.txt
python verify.py
```

This independently recounts 1,044 seven-vertex hosts, checks 184 positive
rational square terms and 826 positive slacks, validates the equality spans,
enumerates all 65,536 Boolean profiles, and checks all 6,496 small-offset
presentations. The report is
[`results/verification_manifest.json`](results/verification_manifest.json).

Run with assertions enabled. No SDP solver, C++ compiler or TeX installation
is required to check supplied witnesses. Linux and Windows CI run the finite
chain and supplementary audits. Run the latter locally with `make audit`.

## Layout

```text
paper/          Anonymous PDF, modular LaTeX, bibliography and figure
blueprint/      Proof route, statement index, evidence map and trust boundary
certificates/   Exact witnesses, graph/flag tensors and finite construction data
src/            Exact verifiers and mathematical specifications
scripts/        Input generators, numerical searches, paper and package tools
results/        Recomputed reports and optional discovery checkpoint
audit/          Supplementary finite checks
docs/           Reproduction conventions and repository design
.github/        Linux and Windows verification workflow
verify.py       Complete verification entry point
```

Numerical search results are discovery aids. See [script documentation](scripts/README.md)
before regenerating witnesses.

## Build the paper

With `latexmk`, pdfLaTeX, BibTeX and the packages used by `paper/main.tex`:

```sh
make all
```

This builds the modular paper, flattens its source, compares the two editions,
and reruns finite verification. For Overleaf, upload `paper/` and select
`submission.tex`. Fresh TeX compilation is separate from certificate checking.

## Documentation and license

- [Detailed reproduction](docs/COMPUTATIONAL_REPRODUCTION.txt)
- [Layout precedents](docs/REPOSITORY_DESIGN.md)
- [Code: MIT; paper and data: CC BY 4.0](LICENSE)

These materials are distributed through GitHub. No preprint-server publication
or archival DOI is required to use them.

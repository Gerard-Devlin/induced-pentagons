# Generation and discovery tools

Run from the repository root. Checking supplied witnesses uses `python verify.py`.

| Purpose | Entry points | Extra requirements |
| --- | --- | --- |
| Inputs | `build_flag_basis.py`, `build_pattern_columns.py`, `build_equality_host_support.py` | C++17 compiler for counting accelerators |
| Discovery | `build_symmetry_blocks.py`, `search_certificate*.py` | Search requirements and selected SDP solver |
| Rationalization | `../src/rationalize_certificate.py` | Checking dependencies; optional FLINT |
| Equality spans | `../src/generate_equality_spans.py` | SymPy; optional FLINT |
| Finite export | `export_finite_data.py` | Python standard library |
| Paper | `build_paper.py`, `flatten_latex.py`, `make_phase_figure.py` | TeX; Matplotlib for figures |
| Archive | `package_checkpoint.py --label LABEL --require-verified` | Current complete verification manifest |

Discovery may produce different valid coefficients. Rerun the complete check
after replacing any witness or input. Floating-point output is not a proof.

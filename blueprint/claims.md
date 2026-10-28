# Claims, evidence, and verification scope

The paper is `paper/submission.pdf`. Its canonical modular source is
`paper/submission.tex`, which loads `main.tex`. All theorem numbers below
refer to that manuscript. `PROOF_DEPENDENCY_GUIDE.txt` locates every statement.

| Claim | Mathematical argument | Finite evidence and checker |
| --- | --- | --- |
| Sharp weighted and graphon bound, Theorems 1.1 and 1.3 | Sections 2-5: attainment, variations, active density, positive slope | `certificates/all_graph_exact_certificate.json`; `verify_combinatorial_inputs.py`, `rationalize_certificate.py --verify-only`, `verify_certificate_independent.py` |
| Triangle elimination and equality, Sections 6-7 | Vanishing conditional squares, triangle elimination, degree/codegree identities, twin quotient | `certificates/all_graph_path3_triangle_domination_span.json`, `certificates/all_graph_tf_degree_codegree_spans.json`; `generate_equality_spans.py --verify-only`, `audit_equality_spans.py` |
| Edge and structural stability, Theorems 8.1 and 9.3 | Peeling, cut compactness, Appendix A, whole-vertex rounding | `verify_stability_inputs.py` checks the finite neighborhood, pair, and Hessian inputs; it does not prove the compactness or stability deduction |
| Arithmetic deficit law, Theorem 10.1 | Structural energy, integer class variance, explicit constructions | `verify_stability_inputs.py` checks finite arithmetic examples |
| Profile envelope and phase law, Lemma 11.1 and Theorem 12.2 | Fractional multilinearity, scalar optimization, uniform counting errors | `verify_profiles.py`, `verify_profile_envelope.py`; all 65,536 Boolean profiles |
| Fixed offsets and eventual polynomiality, Theorems 13.1 and 14.1 | Strong stability, bounded defect family, exact counting polynomial, eventual lexicographic maximum | `verify_offsets.py`, `verify_presentation_census.py`, `verify_offset_polynomials.py`; complete stored data for offsets -2 through 2 |

All programs named in the table are in `src/`. Run the complete finite chain
with `python src/verify_project.py` from the repository root.

## What a successful run establishes

The finite host atlas is exhaustive, its primitive counts match independently
recounted integer tensors, every exact certificate identity and coefficient
sign holds, and the stored finite constructions agree with their formulas.
The SHA256 map binds the reviewed source, data, manuscript, and documentation
bytes. It is an integrity record, not a signature or a proof of the prose.

The independent certificate checker uses a different contraction of the same
raw input tensors. The independent combinatorial recount checks those tensors
and a separate mathematical specification. These checks reduce shared-code
risk; they still rely on the stated interpretation of the formulas.

## What a successful run does not establish

The [Lean certificate layer](../formal/README.md) checks the SOS and equality-span
arithmetic on imported exact tensors. It does not formalize the tensor recount
or the whole paper. The infinite-dimensional
variation, trace-limit, compactness, local repair, and eventual-extremality
arguments require mathematical reading. The fixed-offset program computes
eventual polynomials; it does not certify a numerical threshold `k_0(j)`.
Finite checks at selected class sizes cannot supply that missing threshold.

The complete [remaining Lean obligations](LEAN_ROADMAP.md) distinguish imported
finite data, certificate arithmetic, and the unformalized analytic deductions.

Numerical SDP output is discovery material. It is unnecessary for checking the
supplied witnesses and is not accepted as evidence of the exact inequality.

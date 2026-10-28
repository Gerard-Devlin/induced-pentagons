# Proof blueprint

Read the stages in order, then use the [statement index](proof_dependencies.txt)
to locate individual lemmas and equations. The [JSON inventory](statements.json)
contains locators generated from the canonical LaTeX sources.

| Stage | Paper | Depends on | Evidence |
| --- | --- | --- | --- |
| Clebsch construction | Section 1 | Definitions | Exact finite counts |
| Attainment and variations | Section 2 | Universal links | Analytic argument |
| Active density | Section 3 | Global variations | Analytic trace limit; exact foundation fixtures |
| Positive-slope identity | Section 4 | Finite specification | Rational certificate, two checkers and independent recount |
| Sharp bound | Section 5 | Attainment, active density, identity | Analytic argument and certificate |
| Triangle elimination | Section 6 | Vanishing squares | Triangle-domination span |
| Equality classification | Section 7 | Triangle elimination | Degree/codegree spans and twin quotient |
| Local repair | Appendix A | Clebsch finite counts | Neighborhood, pair and Hessian checks |
| Global stability | Sections 8-9 | Equality and local repair | Peeling, compactness and rounding |
| Arithmetic deficit | Section 10 | Structural stability | Integer variance and constructions |
| Profile envelope | Sections 11-12 | Clebsch counts | 65,536 Boolean profiles and multilinearity |
| Phase law | Section 12 | Stability and profile envelope | Uniform analytic counting estimates |
| Fixed offsets | Section 13 | Stability and local coefficients | Integral lattice optimization |
| Eventual polynomials | Section 14 | Bounded defects | 6,496 small-offset presentations and exact formulas |

Most analytic rows remain mathematical arguments in the manuscript. The
[Mathlib component project](../formal/paper/README.md) proves the full profile
envelope and scalar profile statements, including the induced-subset
interpretation and attaining profiles. It also proves the general equivalence
of labelled, canonical and induced-subset pentagon polynomials. The remaining
graph and analytic dependencies are listed in the coverage roadmap.
See the [claims map](claims.md) and [trust boundary](trust.md).

The [Lean certificate layer](../formal/README.md) covers the exact SOS arithmetic
and equality-span witnesses on imported tensors. The [Lean roadmap](LEAN_ROADMAP.md)
records the finite-graph semantics and analytic proofs still to be formalized.

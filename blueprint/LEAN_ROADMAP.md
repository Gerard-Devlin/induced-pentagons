# Lean coverage and remaining proof obligations

The implemented layer is described in [formal/README.md](../formal/README.md).
Its theorem checks the actual main finite SOS and equality-span arithmetic on
imported exact tensors. It does not state the paper's graph inequality.

| Layer | Current status | Obligation still required for a full formal proof |
| --- | --- | --- |
| Clebsch construction | Finite graph model and counts formalized | Complete normalized pentagon enumeration gives 192; degree, edges, triangles and codegrees are proved; the full balanced-blow-up cardinality formulas remain to be derived |
| Blow-ups and isolates | Embedding correspondences formalized | Projection is injective on pentagon vertices; lift/project and add/remove-isolate maps are inverse; connect these to the full numerical weighted formulas |
| Exact arithmetic | Kernel checked in Lean | Rational bindings, signs, slope, 10,722 Gram entries, 1,044 host identities and four equality-span witnesses are covered by the current checker |
| Data transcription | Reproducible export and hashes | The export is checked against JSON/NPZ; a formal parser and semantic input derivation would further reduce the transcription boundary |
| Seven-vertex atlas | Python independent recount | Define graph-mask relabelling, prove canonical representative coverage and orbit disjointness, and establish the 1,044-host census in Lean |
| Primitive patterns and flag tensors | Python independent recount | Prove injection counts, rooted canonicalization, disjoint-extension products, and all normalizations from finite graph definitions |
| Finite identity interpretation | Not formalized | Derive the polynomial/density identity from the host identities, including nonnegativity of conditional squares and the permitted variational terms |
| Equality-kernel interpretation | Not formalized | Relate the imported kernel constraints and additional degree identities to the equality model and equality hypotheses |
| Global bound, Sections 2-5 | Not formalized | Weighted/graphon definitions, attainment, variations, trace limit, active density and positive-slope deduction |
| Equality classification, Sections 6-7 | Arithmetic spans covered; deduction not formalized | Conditional square vanishing, triangle elimination, degree/codegree identities, and the Clebsch twin quotient |
| Stability, Sections 8-9 and Appendix A | Not formalized | Local repair, compactness, peeling, whole-vertex rounding and the optimal exponent |
| Arithmetic and phase law, Sections 10-12 | Elementary integral variance lemmas formalized | Square-sum parity and the nonzero balanced variance gap are proved; structural energy, graph applications, multilinear profile envelope and uniform asymptotic errors remain |
| Eventual polynomials, Sections 13-14 | Not formalized | Bounded defect reduction, counting polynomial semantics, and eventual maximization; no numerical global threshold is certified |

The next dependency to formalize is the **finite graph semantics of the host and
flag data**, then the passage from coefficient identities to the finite density
inequality. The analytic steps need an appropriate real-analysis/measure-theory
library, such as Mathlib, and new mathematical definitions and proofs.

Incomplete paper obligations are recorded here rather than represented by
`sorry` or unproved axioms in the Lean library. The repository's Lean badge means
that the committed finite-certificate project builds and passes its CI checks.
It must not be presented as certification of the complete manuscript.

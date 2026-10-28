# Lean coverage and remaining proof obligations

The implemented layer is described in [formal/README.md](../formal/README.md).
Its theorem checks the actual main finite SOS and equality-span arithmetic on
imported exact tensors. It does not state the paper's graph inequality.

| Layer | Current status | Obligation still required for a full formal proof |
| --- | --- | --- |
| Clebsch construction | Counts, balanced formulas, counting conventions and sharp equality formalized | Complete enumerations give 192 induced five-cycle subsets and 1,920 labelled embeddings. A general bijection and ten-element fibres prove the weighted labelled/canonical/subset identities; balanced formulas are 40 k² and 192 k⁵, with the exact sharp-constant equality |
| Blow-ups and isolates | Correspondences, cardinalities and weighted class-mass identities formalized | Darts scale by k² and labelled pentagons by k⁵; arbitrary clone weights collapse exactly to class masses. The general convention theorem transfers pentagon identities to induced subsets and canonical tuples |
| Exact arithmetic | Kernel checked in Lean | Rational bindings, signs, slope, 10,722 Gram entries, 1,044 host identities and four equality-span witnesses are covered by the current checker |
| Data transcription | Reproducible export and hashes | The export is checked against JSON/NPZ; a formal parser and semantic input derivation would further reduce the transcription boundary |
| Seven-vertex atlas | Python independent recount | Define graph-mask relabelling, prove canonical representative coverage and orbit disjointness, and establish the 1,044-host census in Lean |
| Primitive patterns and flag tensors | Python independent recount | Prove injection counts, rooted canonicalization, disjoint-extension products, and all normalizations from finite graph definitions |
| Finite identity interpretation | Not formalized | Derive the polynomial/density identity from the host identities, including nonnegativity of conditional squares and the permitted variational terms |
| Equality-kernel interpretation | Not formalized | Relate the imported kernel constraints and additional degree identities to the equality model and equality hypotheses |
| Global bound, Sections 2-5 | Not formalized | Weighted/graphon definitions, attainment, variations, trace limit, active density and positive-slope deduction |
| Equality classification, Sections 6-7 | Arithmetic spans covered; deduction not formalized | Conditional square vanishing, triangle elimination, degree/codegree identities, and the Clebsch twin quotient |
| Stability, Sections 8-9 and Appendix A | Not formalized | Local repair, compactness, peeling, whole-vertex rounding and the optimal exponent |
| Arithmetic and phase law, Sections 10-12 | Integer variance and full Lemmas 11.1/12.1 formalized | Both profile upper bounds, neighborhood attainment, the induced-subset convention bridge and equation (58) are proved. Structural energy, the phase-law counting and uniform asymptotic errors remain; the supplementary Boolean equality catalogue is still a Python result |
| Eventual polynomials, Sections 13-14 | Not formalized | Bounded defect reduction, counting polynomial semantics, and eventual maximization; no numerical global threshold is certified |

The **finite graph semantics of the host and flag data** remain a central
dependency, followed by the passage from coefficient identities to the finite
density inequality. The [Mathlib extension](../formal/paper/README.md) supplies
the real-weighted finite model and completed scalar/expectation arguments.
Attainment, variations and stability still require the measure-theoretic
graphon development and new mathematical proofs.

Incomplete paper obligations are recorded here rather than represented by
`sorry` or unproved axioms in the Lean library. The repository's Lean badge means
that both the committed finite-certificate and Mathlib component projects build
and pass their CI checks.
It must not be presented as certification of the complete manuscript.

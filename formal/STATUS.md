# Formalization status

The complete core finite-certificate build has passed locally with Lean 4.35.0.
The generated arithmetic proofs are checked by Lean kernel reduction.

Locally checked components:

- Rational bindings, coefficient signs, equality-kernel vectors and slope margin.
- Triangle-domination, degree, and both codegree span witnesses.
- Generic ordered-integer SOS nonnegativity and positive-square vanishing lemmas.
- A direct finite-graph model of the Clebsch graph: degree five, 40 edges,
  triangle-freeness, codegrees, and the complete duplicate-free enumeration of
  192 normalized induced pentagons, including its squared sharp normalization.
- General lifting/projection inverse laws for pentagon embeddings in blow-ups;
  a pentagon projects injectively to the base graph.
- Adding arbitrary isolated vertices preserves pentagon embeddings, with
  explicit inverse maps.
- Integer square-sum parity, zero characterization and the nonzero balanced
  integer-variance gap of at least two.

All 10,722 Gram entries and all 1,044 host identities have been checked, and the
aggregate theorem `Generated.coreCertificateVerified` has compiled successfully.

`python scripts/verify_lean.py` additionally audits the transitive axioms of
29 declarations and requires Lean to reject four deliberately corrupted inputs.
Its successful report is `results/lean_verification.json`. The permitted ordinary
Lean axioms are `propext`, `Classical.choice` and `Quot.sound`; placeholder or
compiler-evaluation axioms are not permitted. GitHub CI also performs a standalone
replay using Lean's kernel. The badge reports the actual workflow state.

The larger remaining graph-theoretic and analytic obligations are recorded in
[the roadmap](../blueprint/LEAN_ROADMAP.md).

The [Mathlib extension](paper/README.md) has a separate gate and report,
`results/lean_paper_verification.json`. It proves weighted blow-up cardinality
and class-mass identities, the Clebsch edge and pentagon formulas with the
exact sharp-constant construction equality, Bernoulli multilinear
extension, and the scalar profile optimization with explicit envelope
hypotheses. It also proves the real weighted clique inequality, the Clebsch
independence bound of five and the resulting weighted complement bound.
The later profile layer closes the envelope hypotheses: the complete 480-path
enumeration, endpoint multiplicities, 256 sound checked prefix families and
Bernoulli extension prove both profile upper bounds. Neighborhood profiles attain
the quadratic bound. A proved path-to-induced-subset bijection and polynomial
identity connect these results to the manuscript's convention. Thus Lemmas 11.1
and 12.1, including equation (58), have corresponding complete Lean statements.

The paper's global inequality, equality classification, stability and phase-law
asymptotics still require the obligations in the roadmap. They are not implied
by these profile lemmas or by a successful certificate arithmetic build.

# Formalization checkpoint

This progress branch contains a working Lean/Std checker and reproducibly
generated candidate proofs for the complete core finite certificate layer.

Locally checked with Lean 4.35.0 at this checkpoint:

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

All 10,722 Gram entries have also been checked. The all-host build is still
running. **There is not yet
a successful verdict for the complete Lean certificate layer at this checkpoint.**
The CI badge reports the actual workflow state, not an asserted proof status.
The project contains no placeholder proofs for the pending arithmetic checks.

The larger remaining graph-theoretic and analytic obligations are recorded in
[the roadmap](../blueprint/LEAN_ROADMAP.md).

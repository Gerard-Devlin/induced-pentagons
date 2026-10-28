# Formalization checkpoint

This progress branch contains a working Lean/Std checker and reproducibly
generated candidate proofs for the complete core finite certificate layer.

Locally checked with Lean 4.35.0 at this checkpoint:

- Rational bindings, coefficient signs, equality-kernel vectors and slope margin.
- Triangle-domination, degree, and both codegree span witnesses.
- Generic ordered-integer SOS nonnegativity and positive-square vanishing lemmas.

The aggregate Gram-row and all-host build is still running. **There is not yet
a successful verdict for the complete Lean certificate layer at this checkpoint.**
The CI badge reports the actual workflow state, not an asserted proof status.
The project contains no placeholder proofs for the pending arithmetic checks.

The larger remaining graph-theoretic and analytic obligations are recorded in
[the roadmap](../blueprint/LEAN_ROADMAP.md).

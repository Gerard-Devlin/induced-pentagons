# Mathematical proof layer

This is the Mathlib-based extension of the standalone certificate project in
the parent directory. It imports the finite graph definitions there; it does
not import an external graphon development or assume the manuscript's main
inequality.

Both Lean and Mathlib are pinned to 4.35.0. The committed Lake manifest fixes
Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679` and pins its dependencies.

## Check

From this directory, with the pinned Lean toolchain installed:

```sh
lake update
cd ../..
python scripts/fetch_mathlib_cache.py
cd formal/paper
lake build
lake env lean Audit.lean
```

The cache command downloads official compiled Mathlib dependencies. Lean checks
the project proofs against those pinned dependencies. To keep the download cache
in a chosen writable directory, set `MATHLIB_CACHE_DIR` before running Lake.

From the repository root, the build, forbidden-proof scan, transitive axiom audit
and source fingerprint gate is:

```sh
python scripts/verify_lean_paper.py
```

The report is `results/lean_paper_verification.json`. The workflow runs this gate
separately from the much larger certificate arithmetic build. The permitted
ordinary axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proved components

- `FiniteGraph.lean`: interpret the independently defined Boolean graph model
  as a Mathlib `SimpleGraph`.
- `WeightedGraph.lean`: explicit equivalences and cardinality identities for
  darts and induced pentagon embeddings in arbitrary finite blow-ups; preservation
  of pentagon embeddings under adding isolates; real weighted edge and pentagon
  sums, their nonnegativity and degree-two/degree-five homogeneity; exact collapse
  to class masses; invariance of the squared ratio under nonzero scaling; and the
  Clebsch edge formula `40 k²`, including balanced finite blow-ups.
- `PentagonCount.lean`: a complete duplicate-free enumeration of labelled
  embeddings for any finite graph, its cardinality interpretation, and the
  kernel-checked Clebsch count of 1,920 labelled embeddings. This proves the
  weighted and balanced-blow-up pentagon formula `192 k⁵`.
- `SharpConstruction.lean`: the exact constant `3/(50 sqrt(10))`, its squared
  value, and the balanced Clebsch equality `C = c* E² sqrt(E)` for nonnegative
  class weights. The squared ratio is `9/25000` for nonzero balanced weights.
- `Bernoulli.lean`: independent Bernoulli weights sum to one; Boolean cylinder
  expectations equal their multilinear monomials; finite sums preserve that
  identity; every Boolean bound transfers to the fractional polynomial. No
  graph-specific Boolean bound is assumed as a theorem in this module.
- `ScalarProfile.lean`: subadditivity of the periodic quadratic cost; reduction
  of arbitrary nonnegative profile sizes to their fractional total; exact scalar
  optimization for every integer offset; and equation (58) from the two explicit
  hypotheses `c ≤ (12/5)d²` and `c ≤ 60`, with `d ≥ 0`. The graph-specific
  interpretation of these hypotheses is still required for the full Lemma 12.1.
- `WeightedClique.lean`: the weighted clique inequality for arbitrary
  nonnegative real weights. Integral blow-ups reduce it to Mathlib's finite
  Turán theorem; normalized integer rounding and a proved limit give real weights.
- `IndependentSets.lean`: completeness of a pruned independent-set enumeration;
  a kernel check on that complete family proves every Clebsch independent set
  has at most five vertices, hence its complement has no six-clique.
- `ClebschComplement.lean`: combines these proofs to derive
  `6 E_complement(x) ≤ (12/5)(sum x)²`, the quadratic bound used in Lemma 11.1.

The pentagon mass uses the standard labelled-embedding sum divided by ten.
The Clebsch numerical formula now follows from a direct labelled count, alongside
the standalone project's separate 192-cycle normalized enumeration. A general
bijection between the two cycle conventions, including equality of arbitrary
weighted normalized-cycle polynomials, remains to be supplied.
The profile-to-complement comparison, finite Boolean profile bound and
attainment profiles are still required to close the profile-envelope dependency.

The complete paper is **not yet formalized**. See the
[coverage roadmap](../../blueprint/LEAN_ROADMAP.md). This project contains only
completed component proofs, with remaining obligations kept in the roadmap.

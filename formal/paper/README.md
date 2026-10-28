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
python -m pip install numpy==2.3.5
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
- `CycleSymmetry.lean`, `PentagonConvention.lean`, and `PentagonSubsetCount.lean`:
  exactly ten adjacency-preserving self-maps of the five-cycle; a bijection
  between canonical cycle tuples and vertex subsets inducing a five-cycle;
  and exactly ten labelled embeddings over each such subset. For arbitrary
  real vertex weights, the labelled sum divided by ten equals both the
  induced-subset polynomial and the canonical-tuple polynomial. In particular,
  the labelled count is ten times the canonical count for every finite graph,
  and the Clebsch graph has 192 induced five-cycle vertex subsets.
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
  interpretation of these hypotheses is supplied by the later profile modules.
- `WeightedClique.lean`: the weighted clique inequality for arbitrary
  nonnegative real weights. Integral blow-ups reduce it to Mathlib's finite
  Turán theorem; normalized integer rounding and a proved limit give real weights.
- `IndependentSets.lean`: completeness of a pruned independent-set enumeration;
  a kernel check on that complete family proves every Clebsch independent set
  has at most five vertices, hence its complement has no six-clique.
- `ClebschComplement.lean`: combines these proofs to derive
  `6 E_complement(x) ≤ (12/5)(sum x)²`, the quadratic bound used in Lemma 11.1.
- `ProfileData.lean`, `ProfileQuadratic.lean`, and `ProfileAttainment.lean`:
  a complete, duplicate-free graph-defined enumeration of 480 induced paths;
  exactly six paths per nonadjacent endpoint pair; the quadratic profile bound;
  and the neighborhood profiles attaining it at every degree in `[0,5]`.
- `BooleanPatternBound.lean`, `PatternPrefix.lean`, and the profile mask modules:
  a sound Boolean branch checker, exact graph-to-mask and literal correspondence,
  and 256 checked prefix families proving the uniform bound sixty. Each prefix
  family is separately proved equal to the relevant filter of the original
  masks. Eight Boolean case splits exhaust all prefixes. Bernoulli extension
  then gives the bound for all fractional profiles.
- `PathConvention.lean`: a bijection between canonical path tuples and vertex
  subsets whose induced simple graph is isomorphic to the four-vertex path.
  Within-subset degree identifies endpoints and internal vertices, and the two
  profile polynomials are proved equal.
- `ProfileTheorems.lean`: the full profile-envelope statement and its attaining
  construction (Lemma 11.1), plus the scalar profile statement in exactly the
  form of equation (58) (Lemma 12.1), using the induced-vertex-subset convention.
  The Clebsch envelope hypotheses of the earlier scalar component are discharged.
- `FiniteAtlas.lean` and the generated atlas modules: Boolean graph equivalences,
  lexicographic edge masks, restriction and one-vertex extension, complete
  enumeration of the possible new neighborhoods, and a sound permutation
  checker. All 11,291 extension witnesses through order seven are checked in the
  kernel, proving coverage of every seven-vertex graph by the 1,044 listed masks.
- `AtlasCertificate.lean`: the proved atlas list equals the actual host array in
  the arithmetic certificate; hence every seven-vertex graph is isomorphic to
  one of those certificate hosts. It also ties the five-vertex mask interpretation
  to the existing `edge5` helper and checks rejection of noninjective maps,
  incorrect adjacency, and absent targets.
- `PatternSemantics.lean`: finite injection counts for partial required-edge and
  nonedge patterns, explicit equivalences under graph isomorphism, and weighted
  isomorphism invariance. The complete five-cycle pattern is identified with
  the earlier pentagon embeddings, including its weighted factor of ten.
- `AtlasInterpretation.lean`: represents arbitrary Mathlib simple graphs by the
  Boolean model and transfers the seven-vertex coverage theorem to them.
  Injection counts of every partial pattern on every seven-vertex graph reduce
  to a host on the actual certificate list.
- `PatternEnumeration.lean` and `PatternSteps.lean`: a complete duplicate-free
  injection enumeration, pruning repeats and failed constraints at every prefix.
  The ordered-step version checks only constraints newly made decidable; its
  output is proved equal to the full prefix checker.
- `PatternNormalization.lean`: the unconstrained injection count is the falling
  factorial, every pattern count is bounded by it, and the resulting rational
  injection density lies in `[0,1]`.
- `PrimitiveCounts.lean`, `PrimitiveFast.lean`, and `Generated/PrimitivePatterns.lean`:
  all 22 explicit required-edge/nonedge specifications from the normative
  specification, their ordering precondition, the exact injection denominators,
  and sound host-row checkers linked to the mathematical counts.
- `Generated/PrimitiveExamples.lean`: all 22 counts for each of the empty and
  complete seven-vertex hosts, connected directly to the shared certificate
  host rows. A changed count with the original array length is rejected.

The pentagon mass uses the standard labelled-embedding sum divided by ten.
The general convention bridge proves that this is the induced-subset count,
with the same identity for arbitrary real vertex weights. The direct labelled
Clebsch count and the standalone 192-cycle normalized enumeration therefore
have a proved connection through these general identities.
The profile envelope and scalar profile dependencies are now closed. The
separate Boolean equality catalogue in the Python verification report is not
claimed as a Lean equality-classification theorem.
Atlas coverage does not yet prove pairwise nonisomorphism of the 1,044 masks,
their canonical minimality or their stored automorphism orders. The generic
primitive checker has certified two of the 1,044 host rows. The other 1,042
rows and the flag-product tensors are not yet certified in Lean.

## Reproduce the profile candidates

```sh
python scripts/export_lean_profiles.py --check
```

Run this command from the repository root. The generated lists are candidates:
Lean proves their equality with graph-defined data and filtered prefix families,
then independently checks each remaining Boolean branch problem in its kernel.
The exporter supplies no assumed counts or proof verdicts. Its manifest binds
the generator and all nineteen generated modules. The mathematical verification
gate runs this regeneration check before building and auditing the proofs.

## Reproduce the atlas candidates

```sh
python scripts/export_lean_atlas.py --check
```

The exporter builds candidate representatives recursively and records an explicit
permutation for each one-vertex extension. The final masks must match the
committed JSON atlas. Its manifest binds that input, the exporter and all 25
generated modules. Lean checks the candidate maps, target membership and every
adjacency relation; a general induction then proves coverage for arbitrary
Boolean graphs. A separate kernel equality connects these masks to the
certificate host array. No Python coverage verdict is assumed.

## Reproduce the primitive pattern specifications

```sh
python scripts/export_lean_patterns.py --check
```

This exporter takes the explicit patterns from `src/proof_specification.py`,
checks their correspondence with the saved metadata and emits the Lean
specifications and two host-row examples. The supplied numerical values are
candidates: Lean recomputes them from the proved enumeration and separately
connects them to the actual `HostData` rows. The manifest binds the specification,
metadata, exporter and generated modules. No supplied counting verdict is used.

The complete paper is **not yet formalized**. See the
[coverage roadmap](../../blueprint/LEAN_ROADMAP.md). This project contains only
completed component proofs, with remaining obligations kept in the roadmap.

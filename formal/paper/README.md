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
- `Generated/PrimitiveRows000.lean` through `PrimitiveRows086.lean`,
  `Generated/PrimitiveComplete.lean`, `PrimitiveTable.lean`, and
  `PrimitiveCertificate.lean`: all 22,968 counts on all 1,044 actual certificate
  rows, their exact indices and masks, and universal count and normalized-density
  semantics for arbitrary seven-vertex Boolean graphs and Mathlib simple graphs.
- `GraphEncoding.lean`: graph-to-mask encoding with a proved adjacency identity;
  the lexicographic pair-index separation and bounds for orders four and five.
- `RootedFlags.lean`, `RootedFlagSeparation.lean`, and generated `Flag*.lean`:
  root-preserving graph equivalences; all 576 coverage witnesses for the five
  actual flag bases; complete root-preserving permutation lists; arbitrary-graph
  coverage; and pairwise rooted nonisomorphism. Wrong adjacency and a map moving
  a root are rejected. These are basis theorems, not flag-product count theorems.
- `RootedClassification.lean`, `PatternSeparation.lean`, `FiveVertexTypes.lean`,
  and `Generated/FixedTypeData.lean`: a checked lookup for all 1,024 labelled
  five-vertex graphs; classification by the certificate's actual 34 masks; and
  pairwise nonisomorphism, certified by nine exact pattern-count invariants.
- `SubsetGraphs.lean`, `FixedDensity.lean`, and `FixedDensityIsomorphism.lean`:
  the sorted subset graph is proved isomorphic to Mathlib's induced graph;
  subset checks are exactly the induced-graph-type predicate; both kinds of
  counts are proved to be cardinalities of those subsets and invariant under
  graph isomorphism. A structurally recursive insertion sort is proved equal
  to Mathlib's canonical sort and permits reduction in the kernel.
- `Generated/FixedRows000.lean` through `FixedRows086.lean`,
  `Generated/FixedComplete.lean`, and `FixedDensityCertificate.lean`: all 35,496
  induced-type counts and all 35,496 complementary-edge counts on the actual
  1,044 host rows, with transfer to every seven-vertex graph. Two same-length
  corrupted arrays are rejected.
- `FixedDensityNormalization.lean` and `FixedColumnAlgebra.lean`: the 34 types
  partition the five-subsets, normalized type densities sum to one, and the
  actual fixed certificate columns have their exact rational density meanings.
  On seven-vertex hosts the complementary-edge condition concerns exactly the
  two omitted vertices; no identification with an outside-edge sampling density
  for larger graphs is claimed by this subset-count model.

The pentagon mass uses the standard labelled-embedding sum divided by ten.
The general convention bridge proves that this is the induced-subset count,
with the same identity for arbitrary real vertex weights. The direct labelled
Clebsch count and the standalone 192-cycle normalized enumeration therefore
have a proved connection through these general identities.
The profile envelope and scalar profile dependencies are now closed. The
separate Boolean equality catalogue in the Python verification report is not
claimed as a Lean equality-classification theorem.
Atlas coverage and pairwise nonisomorphism now give a unique certificate host
for every seven-vertex Boolean graph and Mathlib simple graph. Canonical
minimality and stored automorphism orders are still unproved. All primitive
host rows, all five rooted flag bases and all fixed-density entries are certified.
The complete flag-product tensor table and its full sampling interpretation remain.

The later flag-product prerequisites are proved in `FlagIndex.lean`,
`JointFlagSampling.lean`, `JointFlagGraphs.lean`, `JointFlagEnumeration.lean`
and `FlagProductSemantics.lean`. The checked classifiers give indices into each
actual certificate basis, and these indices characterize rooted isomorphism.
A joint sample is an ordered root injection plus an unordered extension subset;
the other extension subset is its disjoint complement. A complete executable
enumeration equals the full abstract sample space. Root-type guards depend only
on roots, and swapping the two extension sets is an involution. Thus oriented
flag-pair counts have proved rooted-isomorphism semantics, symmetry and bounds.
The sample totals 140 and 1,260 equal the actual certificate block denominators;
they include all root injections, with incompatible root types contributing zero.
`FlagProductExamples.lean` directly recounts the two saved nonzero entries on
the empty host and binds them to its actual `HostData` row. Its implicit zeros
and the other 1,043 hosts remain unchecked. The upper-triangular combination,
universal count transfer and full-permutation fiber bridge also remain open.

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

## Reproduce the host-separation candidates

```sh
python scripts/export_lean_host_codes.py --check
```

The exporter proposes integer encodings of the 90 existing count invariants and
a sorted order of the 1,044 hosts. Lean checks the encoding of every actual raw
row, a permutation of the complete list and strict increase of the codes.
`AtlasSeparation.lean` combines these checks with the proved count invariance to
prove pairwise nonisomorphism and unique representatives. Code injectivity on all
possible vectors is not assumed or needed for this separation implication.

## Reproduce the primitive pattern specifications

```sh
python scripts/export_lean_patterns.py --check
```

This exporter takes the explicit patterns from `src/proof_specification.py`,
checks their correspondence with the saved metadata and emits the Lean
specifications, two endpoint examples and the complete 1,044-row table in 87
batches. Eight import chains bound concurrent kernel jobs. The supplied values are
candidates: Lean recomputes them from the proved enumeration and separately
connects them to the actual `HostData` rows. The manifest binds the specification,
metadata, exporter and generated modules. No supplied counting verdict is used.

## Reproduce the rooted flag candidates

```sh
python scripts/export_lean_flags.py --check
```

This exporter reads the normative five flag specifications and the stored basis
masks, and supplies candidate root-preserving isomorphisms. Lean checks all 576
witnesses, equality of their sources with the complete relevant mask families,
and equality of the basis lists with the actual certificate blocks. The graph
encoding theorem transfers coverage to arbitrary graphs. Lean checks completeness
of the root-preserving permutation lists and separation of every pair of basis
members. This proves uniqueness up to rooted isomorphism; numerical minimality
of each mask is not needed or claimed. The manifest binds the exporter, the
normative specification, the NPZ input and all seven generated modules.

## Reproduce the indexed flag classifiers

```sh
python scripts/export_lean_flag_indices.py --check
```

The exporter supplies 4,160 lookup slots, including all 576 valid-root masks.
Lean checks each valid-root witness and its output index against the actual
certificate basis. Invalid-root slots are guarded. Generic theorems prove that
the returned index characterizes rooted isomorphism and is invariant under it.
A changed index is rejected even when the old graph-isomorphism witness remains
unchanged. The manifest binds the exporter, specification, NPZ and six modules.

## Reproduce the fixed-density candidates

```sh
python scripts/export_lean_fixed.py --check
```

The exporter supplies 1,024 graph-classification witnesses, candidate invariant
signatures and all 70,992 fixed-density entries from the saved NPZ input. Lean
checks the witnesses and signatures, proves classification correctness, then
recounts the actual five-subsets of every host. Raw `HostData` equalities bind
the results to the arithmetic certificate. Eight import chains bound concurrent
kernel jobs. The manifest binds the exporter, its inputs and all 89 generated
modules. No numerical classification or counting verdict from Python is assumed.

The complete primitive-table build is substantially larger than the old two-host
examples. The paper CI job allows 180 minutes for a cold build, followed by its
transitive axiom audit; subsequent local builds reuse current compiled modules.

The complete paper is **not yet formalized**. See the
[coverage roadmap](../../blueprint/LEAN_ROADMAP.md). This project contains only
completed component proofs, with remaining obligations kept in the roadmap.

The finite weighted-graph analysis layer proves continuity of edge and pentagon
polynomials, coordinatewise limit transfer, and continuity of the squared ratio
at positive edge mass. Nonnegative unit-mass weights form a compact set; at every
feasible prescribed edge mass, the pentagon polynomial attains a maximum.
These are fixed finite-graph results. Graphon attainment and trace limits remain
separate obligations in the roadmap.

The rounded-weight bridge also proves that any homogeneous squared pentagon
bound checked for all nonnegative integer weights is equivalent to its real
nonnegative-weight form.

Variable-size integral blow-ups now have exact pentagon-count semantics through
an explicit dependent equivalence. Together with rounded-weight convergence,
this gives a proved reduction from a universal unweighted finite-graph squared
pentagon bound to its universal nonnegative real-weighted version.

The zero-edge boundary is proved directly: nonnegative weights with zero edge
mass have zero pentagon mass. The sharp square-root bound is equivalent to its
squared polynomial form everywhere, and to the normalized squared-ratio form
on positive edge mass.

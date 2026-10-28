# Lean certificate verification

See [STATUS.md](STATUS.md) for the checked components and the separate
verification report. A full PASS requires the complete build, axiom audit and
corruption rejection gate.

This Lean 4 project checks the **core finite certificate layer** of the paper.
It is not a formalization of the complete induced-pentagon theorem, its graphon
extension, stability, or eventual extremality.

The [separate Mathlib project](paper/README.md) in `paper/` extends this layer
with real weighted graph identities, Bernoulli multilinearity and the scalar
optimization used in Lemma 12.1. It has its own build and axiom-audit gate.

## Run

Install the toolchain pinned in `lean-toolchain` using the official Lean/Elan
installation instructions. This parent project has no Mathlib or third-party Lean packages.
From this directory run:

```sh
lake build
lake env lean Audit.lean
```

From the repository root, the complete reproducibility and rejection gate is:

```sh
python scripts/export_lean_certificate.py --check
python scripts/verify_lean.py
```

The exporter needs NumPy, as specified in the repository's verification
requirements. Building the committed Lean sources needs only Lean and Std.
The generated sources contain large exact integers; a fresh kernel build is
more expensive than the existing Python checks. Set `LEAN_NUM_THREADS=2` when
building on a machine with limited memory. Host batches have sequential import
dependencies to bound simultaneous large kernel jobs.

## What the theorem checks

`InducedPentagons.Generated.coreCertificateVerified` has the explicit type
`coreCertificateChecks = true`. That Boolean is the conjunction of all the
following checks on the actual exported data:

- Rational numerator/denominator bindings to a common positive integer scale;
  37 free coefficients, four nonnegative variational coefficients, 184 strictly
  positive square weights, and 1,044 nonnegative slacks, of which 826 are positive.
- Required coefficient bounds and the cleared positive-slope margin.
- Each square vector's membership in the supplied equality kernel.
- All 10,722 upper-triangular Gram coefficients recomputed from the positive
  square vectors and their weights, checked in 308 rows.
- All 1,044 host identities, checked in 87 batches of 12. The checker reconstructs
  the variational columns from raw primitive pattern counts and the fixed-density
  counts, then contracts the sparse flag tensors against the verified Gram entries.
  It does not import Python residuals or Python PASS values.
- The triangle-domination vector on 72 flags, the degree span on 24 triangle-free
  path flags, and both codegree spans on 32 triangle-free edge-isolate flags.
  Sources must refer to strictly positive squares in the same main certificate;
  the two additional degree identities in the codegree spans are labelled explicitly.

The data denominator is 557,383,680. This clears every primitive rational factor
individually; it is twice the denominator of the already combined Python columns.
Divisibility, dimensions, source references, and the relevant flag-mask predicates
are themselves checked. Tensor entries for `(i,j)` and `(j,i)` are combined in
upper-triangular storage; the Gram expression is a sum of `weight * v_i * v_j`.

`Soundness.lean` additionally proves ordered-integer lemmas for nonnegative
weighted squares and vanishing of a positive square at equality. These elementary
lemmas do not supply a graphon or real-density interpretation of the data.

## Additional mathematical proofs

The library also contains proofs independent of the imported certificate tensors:

- `FiniteGraph.lean` defines symmetric loopless finite graphs and induced
  pentagon embeddings. It proves the completeness of the normalized-cycle
  enumeration, injectivity of pentagon embeddings, and projection/lifting
  inverse laws for arbitrary blow-ups. A pentagon in a blow-up uses five
  distinct base vertices.
- `Construction.lean` derives the Clebsch model directly from XOR adjacency.
  Its degree, 40 edges, triangle-freeness and codegrees are kernel checked.
  Lean checks equality of the complete induced-cycle enumeration with a
  candidate list, proves that it has 192 entries without duplicates, and
  verifies the squared sharp-constant normalization. The convention chooses
  the smallest vertex first and orders the two orientations.
- `Isolates.lean` proves that adding any family of isolated vertices does not
  change the induced-pentagon embeddings, using explicit inverse maps.
- `IntegerVariance.lean` proves square-sum parity, its zero characterization,
  and the gap `sum x_i^2 >= 2` for a nonzero integral vector whose sum is zero.

The candidate Clebsch list is generated for convenience, but the proof checks
the complete graph-defined enumeration against it. Its count is not an imported
Python counting verdict. These results do not yet supply the general tensor
semantics, full balanced-blow-up cardinality formulas or analytic upper bound.

The generated arithmetic proofs use `decide +kernel`; the aggregate theorem
combines those proofs. No `sorry`, assumed certificate
axioms, `native_decide`, external solver verdicts, or compiler-evaluation axioms
are used. `Audit.lean` prints the transitive axioms of the aggregate theorem,
span checks, and soundness lemmas. CI also checks that corrupted input examples
cannot be proved and rechecks the compiled environment with Lean's `leanchecker`.
This is a separate replay using the same Lean kernel, not a second independent
implementation of the type checker.
The permitted ordinary Lean axioms are `propext`, `Classical.choice`, and
`Quot.sound`; any other transitive axiom makes the audit fail.

## Input correspondence and trust boundary

The generated input file embeds the rational coefficients, square vectors,
host masks, raw primitive counts, fixed-density counts and sparse tensor entries
from the existing JSON and NPZ inputs. The exporter builds candidate Gram tables;
Lean independently recomputes every entry. A wrong candidate does not yield a proof.

`Generated/manifest.json` records SHA256 values for all five source input files
and every generated Lean file. `export_lean_certificate.py --check` regenerates
the files and fails on any difference, including stale or extra generated modules.
This binds the transcription to the repository inputs; hashes do not prove that
those inputs have their intended graph-theoretic meaning.

The standalone arithmetic checker does not establish the atlas or tensor
semantics. The [Mathlib extension](paper/README.md) separately proves universal
seven-vertex atlas coverage and equality with the certificate's host array.
Pairwise nonisomorphism, the orbit census, primitive-pattern counts, canonical
flag bases and tensor sampling interpretation remain to be established in Lean;
the Python gate independently recounts them. Thus this arithmetic layer remains
a result on imported tensors, rather than the paper's graph inequality.

See [the remaining formalization work](../blueprint/LEAN_ROADMAP.md) for the precise
gaps between this project and a full paper formalization.

## Files

```text
lean-toolchain                    Pinned official Lean release
lakefile.toml                     Lean/Std-only library
InducedPentagons/Verifier.lean     Handwritten exact checker and normalizations
InducedPentagons/FastVerifier.lean Gram rows as sums of weighted vector rows
InducedPentagons/Soundness.lean    Generic ordered-integer SOS consequences
InducedPentagons/FiniteGraph.lean Graph semantics, enumeration and blow-ups
InducedPentagons/Construction.lean Direct Clebsch pentagon count
InducedPentagons/Isolates.lean     Isolated-vertex invariance
InducedPentagons/IntegerVariance.lean Integer lattice lemmas
InducedPentagons/Generated/       Reproducible data and kernel proofs
InducedPentagons.lean             Library entry point
Audit.lean                        Transitive axiom audit
```

The code license is the repository's MIT license; mathematical data remain under
the repository's CC BY 4.0 license.

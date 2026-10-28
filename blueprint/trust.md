# Verification trust boundary

`python verify.py` independently recounts integer host and flag tensors from
graph definitions. It checks every rational identity, coefficient sign,
positive square and equality-span combination. Another checker contracts
complete integer Gram matrices against those recounted tensors.

`src/proof_specification.py` specifies the patterns and denominators separately
from the saved metadata and production input generators. Final identities
use arbitrary-precision integers and rational arithmetic. Numerical SDP
output has no role in accepting the exact witness.

The Python implementation relies on Python and its installed libraries.
The separate [Lean project](../formal/README.md) rechecks the core SOS and
equality-span arithmetic in Lean's kernel on the imported exact tensors.
The standalone checker does not prove the tensor interpretation. The separate
Mathlib extension now proves universal atlas coverage, with an explicit kernel
equality to the certificate's actual host list. Canonical minimality, pairwise
nonisomorphism and the automorphism/orbit census remain separate obligations.
Independent counting routes, Linux/Windows CI and 24 malformed-input rejection
cases provide additional implementation checks for the Python layer.

Global attainment, graphon variations, the trace limit, equality
classification, compactness, local repair and uniform asymptotics are argued
in `paper/`. Finite fixtures do not formally verify these deductions.

The eventual-polynomial algorithm does not compute a global validity
threshold `k_0(j)`. The presentation counts retain Clebsch type labels;
they are not counts of pairwise nonisomorphic extremal graphs.

The verification report binds current source, exact data, paper, blueprint,
documentation and build configuration bytes. Changed or newly added inputs
invalidate the binding. Hashes detect changes and do not prove the prose.

The [Mathlib component project](../formal/paper/README.md) adds proofs of finite
weighted identities, Bernoulli multilinearity and scalar profile optimization.
Its separate report and axiom audit cover exactly the declarations listed in
that project. The later profile layer derives the graph-specific envelope from
complete graph-defined path data, verified prefix families and a sound Boolean
checker, and proves correspondence with induced vertex subsets. This closes
the envelope hypotheses for Lemma 12.1, without extending the claim to the
phase-law asymptotics or the paper's global bound.
Its partial-pattern injection model and isomorphism invariance provide finite
semantics for later count proofs. They do not yet certify the saved primitive
count columns or the flag-product tensors.

The Lean badge reports the certificate and component-proof jobs, not the complete paper.
See [the formalization roadmap](LEAN_ROADMAP.md).

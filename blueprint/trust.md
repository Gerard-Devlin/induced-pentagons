# Verification trust boundary

`python verify.py` independently recounts integer host and flag tensors from
graph definitions. It checks every rational identity, coefficient sign,
positive square and equality-span combination. Another checker contracts
complete integer Gram matrices against those recounted tensors.

`src/proof_specification.py` specifies the patterns and denominators separately
from the saved metadata and production input generators. Final identities
use arbitrary-precision integers and rational arithmetic. Numerical SDP
output has no role in accepting the exact witness.

The checking implementation relies on Python and its installed libraries.
It is not checked by a proof-assistant kernel. Independent counting routes,
Linux/Windows CI and 24 malformed-input rejection cases provide additional
implementation checks.

Global attainment, graphon variations, the trace limit, equality
classification, compactness, local repair and uniform asymptotics are argued
in `paper/`. Finite fixtures do not formally verify these deductions.

The eventual-polynomial algorithm does not compute a global validity
threshold `k_0(j)`. The presentation counts retain Clebsch type labels;
they are not counts of pairwise nonisomorphic extremal graphs.

The verification report binds current source, exact data, paper, blueprint,
documentation and build configuration bytes. Changed or newly added inputs
invalidate the binding. Hashes detect changes and do not prove the prose.

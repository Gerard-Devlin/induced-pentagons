import InducedPentagonsPaper.Generated.TensorGeometry

/-! Kernel recounts with the host-independent geometry reduced in advance. -/

namespace InducedPentagons.Paper

def geometryFlagTensorKeys (g : Graph (Fin 7)) : Multiset Nat :=
  vertexPairKeys (roots := 1) (free := 3) 0 (jointRootCheck (free := 3) 0 g)
    (fun f => indexedFlag_one_root (comapBooleanGraph g f)) tensorVertexPairs_one +
  vertexPairKeys (roots := 3) (free := 2) 1 (jointRootCheck (free := 2) 0 g)
    (fun f => indexedFlag_independent3 (comapBooleanGraph g f)) tensorVertexPairs_three +
  vertexPairKeys (roots := 3) (free := 2) 2 (jointRootCheck (free := 2) 1 g)
    (fun f => indexedFlag_edge_isolate (comapBooleanGraph g f)) tensorVertexPairs_three +
  vertexPairKeys (roots := 3) (free := 2) 3 (jointRootCheck (free := 2) 17 g)
    (fun f => indexedFlag_path3 (comapBooleanGraph g f)) tensorVertexPairs_three +
  vertexPairKeys (roots := 3) (free := 2) 4 (jointRootCheck (free := 2) 19 g)
    (fun f => indexedFlag_triangle3 (comapBooleanGraph g f)) tensorVertexPairs_three

theorem geometryFlagTensorKeys_eq (g : Graph (Fin 7)) :
    geometryFlagTensorKeys g = flagTensorKeys g := by
  unfold geometryFlagTensorKeys flagTensorKeys
  rw [← tensorVertexPairs_one_checked, ← tensorVertexPairs_three_checked]
  simp only [vertexPairKeys_eq, JointFlagSample.graph]

def geometryTrieTensorCheck (mask : Nat) (entries : List (Nat × Nat)) : Bool :=
  entries.all (fun e => decide (e.1 < 32768)) &&
    decide (CountTrie.ofWeighted 15 entries = CountTrie.ofKeys 15 (geometryFlagTensorKeys (maskGraph 7 mask)))

theorem geometryTrieTensorCheck_eq (mask : Nat) (entries : List (Nat × Nat)) :
    geometryTrieTensorCheck mask entries = fastTrieTensorCheck mask entries := by
  simp only [geometryTrieTensorCheck, geometryFlagTensorKeys_eq, fastTrieTensorCheck]

end InducedPentagons.Paper

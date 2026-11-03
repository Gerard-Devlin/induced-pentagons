import InducedPentagonsPaper.FlagTensorTrie

/-! Reusable geometric sample presentations for flag-tensor kernel recounts. -/

namespace InducedPentagons.Paper

abbrev JointFlagVertexPair (n roots free : Nat) :=
  (Fin roots ↪ Fin n) × (Fin (roots + free) → Fin n) × (Fin (roots + free) → Fin n)

def jointFlagVertexPairs {n roots free : Nat} (hn : n = roots + 2 * free) :
    Multiset (JointFlagVertexPair n roots free) :=
  (jointFlagSamples n roots free).val.map (fun x => (x.1, x.vertex, (x.swap hn).vertex))

def vertexPairKeys {n roots free dimension : Nat} (block : Nat)
    (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : (Fin (roots + free) → Fin n) → Fin dimension)
    (samples : Multiset (JointFlagVertexPair n roots free)) : Multiset Nat :=
  (samples.filter (fun x => valid x.1)).map (fun x =>
    flagTensorKey block (min (classify x.2.1).val (classify x.2.2).val)
      (max (classify x.2.1).val (classify x.2.2).val))

theorem vertexPairKeys_eq {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (block : Nat) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : (Fin (roots + free) → Fin n) → Fin dimension) :
    vertexPairKeys block valid classify (jointFlagVertexPairs hn) =
      jointFlagPairKeys hn block valid (fun x => classify x.vertex) := by
  simp only [vertexPairKeys, jointFlagVertexPairs, Multiset.filter_map, Multiset.map_map,
    jointFlagPairKeys, Finset.filter_val, Function.comp_def]

end InducedPentagons.Paper

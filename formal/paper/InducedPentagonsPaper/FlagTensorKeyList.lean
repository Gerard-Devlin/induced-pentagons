import InducedPentagonsPaper.FlagTensorFast

namespace InducedPentagons.Paper

def checkedTensorKeyList {n roots free dimension : Nat} (block : Nat)
    (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : (Fin (roots + free) → Fin n) → Fin dimension)
    (samples : List (JointFlagVertexPair n roots free)) : List Nat :=
  (samples.filter (fun x => valid x.1)).map (fun x =>
    flagTensorKey block (min (classify x.2.1).val (classify x.2.2).val)
      (max (classify x.2.1).val (classify x.2.2).val))

theorem checkedTensorKeyList_eq {n roots free dimension : Nat} (block : Nat)
    (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : (Fin (roots + free) → Fin n) → Fin dimension)
    (samples : List (JointFlagVertexPair n roots free)) :
    (checkedTensorKeyList block valid classify samples : Multiset Nat) =
      vertexPairKeys block valid classify (samples : Multiset (JointFlagVertexPair n roots free)) := by
  rfl


def geometryFlagTensorKeyList (g : Graph (Fin 7)) : List Nat :=
  checkedTensorKeyList (roots := 1) (free := 3) 0 (jointRootCheck (free := 3) 0 g)
    (fun f => indexedFlag_one_root (comapBooleanGraph g f)) tensorVertexList_one ++
  checkedTensorKeyList (roots := 3) (free := 2) 1 (jointRootCheck (free := 2) 0 g)
    (fun f => indexedFlag_independent3 (comapBooleanGraph g f)) tensorVertexList_three ++
  checkedTensorKeyList (roots := 3) (free := 2) 2 (jointRootCheck (free := 2) 1 g)
    (fun f => indexedFlag_edge_isolate (comapBooleanGraph g f)) tensorVertexList_three ++
  checkedTensorKeyList (roots := 3) (free := 2) 3 (jointRootCheck (free := 2) 17 g)
    (fun f => indexedFlag_path3 (comapBooleanGraph g f)) tensorVertexList_three ++
  checkedTensorKeyList (roots := 3) (free := 2) 4 (jointRootCheck (free := 2) 19 g)
    (fun f => indexedFlag_triangle3 (comapBooleanGraph g f)) tensorVertexList_three

theorem geometryFlagTensorKeyList_eq (g : Graph (Fin 7)) :
    (geometryFlagTensorKeyList g : Multiset Nat) = flagTensorKeys g := by
  rw [← geometryFlagTensorKeys_eq]
  rfl

theorem fastTrieTensorCheck_of_keyList (mask : Nat) (entries : List (Nat × Nat))
    (keys : List Nat) (hk : geometryFlagTensorKeyList (maskGraph 7 mask) = keys)
    (hb : entries.all (fun e => decide (e.1 < 32768)) = true)
    (hc : CountTrie.ofWeighted 15 entries = CountTrie.ofKeys 15 (keys : Multiset Nat)) :
    fastTrieTensorCheck mask entries = true := by
  unfold fastTrieTensorCheck
  rw [← geometryFlagTensorKeyList_eq, hk, hc, hb]
  simp

end InducedPentagons.Paper

import InducedPentagonsPaper.PackedCounts
import InducedPentagonsPaper.FlagProductSemantics
import InducedPentagonsPaper.JointFlagEnumeration

/-! One-pass exact encodings of all upper-triangular flag-product counts. -/

set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def flagTensorKey (block i j : Nat) : Nat := (block * 72 + i) * 72 + j

theorem flagTensorKey_injective {b i j b' i' j' : Nat}
    (hi : i < 72) (hj : j < 72) (hi' : i' < 72) (hj' : j' < 72)
    (he : flagTensorKey b i j = flagTensorKey b' i' j') :
    b = b' ∧ i = i' ∧ j = j' := by
  unfold flagTensorKey at he
  omega

def jointFlagPairKeys {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (block : Nat) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) : Multiset Nat :=
  (((jointFlagSamples n roots free).filter (fun x => valid x.1)).val).map (fun x =>
    let i := (classify x).val
    let j := (classify (x.swap hn)).val
    flagTensorKey block (min i j) (max i j))

theorem jointFlagPairKeys_card_le {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (block : Nat) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) :
    (jointFlagPairKeys hn block valid classify).card ≤
      n.descFactorial roots * (n - roots).choose free := by
  simp only [jointFlagPairKeys, Multiset.card_map]
  exact (Finset.card_filter_le _ _).trans_eq (jointFlagSamples_card n roots free)

theorem jointFlagPairKeys_bounded {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (block : Nat) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension)
    (hb : block < 5) (hd : dimension ≤ 72) :
    ∀ k ∈ jointFlagPairKeys hn block valid classify, k < 32768 := by
  intro k hk
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hk
  have hi := (classify x).isLt
  have hj := (classify (x.swap hn)).isLt
  dsimp only [flagTensorKey]
  omega

def flagTensorKeys (g : Graph (Fin 7)) : Multiset Nat :=
  jointFlagPairKeys (n := 7) (roots := 1) (free := 3) (by decide) 0
    (jointRootCheck (free := 3) 0 g) (fun x => indexedFlag_one_root (x.graph g)) +
  jointFlagPairKeys (n := 7) (roots := 3) (free := 2) (by decide) 1
    (jointRootCheck (free := 2) 0 g) (fun x => indexedFlag_independent3 (x.graph g)) +
  jointFlagPairKeys (n := 7) (roots := 3) (free := 2) (by decide) 2
    (jointRootCheck (free := 2) 1 g) (fun x => indexedFlag_edge_isolate (x.graph g)) +
  jointFlagPairKeys (n := 7) (roots := 3) (free := 2) (by decide) 3
    (jointRootCheck (free := 2) 17 g) (fun x => indexedFlag_path3 (x.graph g)) +
  jointFlagPairKeys (n := 7) (roots := 3) (free := 2) (by decide) 4
    (jointRootCheck (free := 2) 19 g) (fun x => indexedFlag_triangle3 (x.graph g))

theorem flagTensorKeys_card_le (g : Graph (Fin 7)) : (flagTensorKeys g).card ≤ 5180 := by
  have h0 := jointFlagPairKeys_card_le (n := 7) (roots := 1) (free := 3) (by decide) 0
    (jointRootCheck (free := 3) 0 g) (fun x => indexedFlag_one_root (x.graph g))
  have h1 := jointFlagPairKeys_card_le (n := 7) (roots := 3) (free := 2) (by decide) 1
    (jointRootCheck (free := 2) 0 g) (fun x => indexedFlag_independent3 (x.graph g))
  have h2 := jointFlagPairKeys_card_le (n := 7) (roots := 3) (free := 2) (by decide) 2
    (jointRootCheck (free := 2) 1 g) (fun x => indexedFlag_edge_isolate (x.graph g))
  have h3 := jointFlagPairKeys_card_le (n := 7) (roots := 3) (free := 2) (by decide) 3
    (jointRootCheck (free := 2) 17 g) (fun x => indexedFlag_path3 (x.graph g))
  have h4 := jointFlagPairKeys_card_le (n := 7) (roots := 3) (free := 2) (by decide) 4
    (jointRootCheck (free := 2) 19 g) (fun x => indexedFlag_triangle3 (x.graph g))
  have d0 : (7 : Nat).descFactorial 1 * (7 - 1).choose 3 = 140 := by decide +kernel
  have d3 : (7 : Nat).descFactorial 3 * (7 - 3).choose 2 = 1260 := by decide +kernel
  rw [d0] at h0
  rw [d3] at h1 h2 h3 h4
  simp only [flagTensorKeys, Multiset.card_add]
  omega

theorem flagTensorKeys_bounded (g : Graph (Fin 7)) :
    ∀ k ∈ flagTensorKeys g, k < 32768 := by
  intro k hk
  simp only [flagTensorKeys, Multiset.mem_add] at hk
  rcases hk with (((h | h) | h) | h) | h
  all_goals exact jointFlagPairKeys_bounded _ _ _ _ (by decide) (by decide) k h

def rawFlagTensorEntries (h : HostRow) : List (Nat × Nat) :=
  h.tensor.toList.map (fun e => (flagTensorKey e.block e.i e.j, e.count))

def actualFlagTensorCode (g : Graph (Fin 7)) : Nat := fastCountPowerCode 8192 15 (flagTensorKeys g)

def rawFlagTensorCode (h : HostRow) : Nat := weightedCountCode 8192 15 (rawFlagTensorEntries h)

def fastFlagTensorCheck (mask : Nat) (entries : List (Nat × Nat)) : Bool :=
  entries.all (fun e => decide (e.1 < 32768)) &&
  decide ((entries.map Prod.snd).sum < 8192) &&
  decide (weightedCountCode 8192 15 entries = actualFlagTensorCode (maskGraph 7 mask))

def fastFlagTensorRowCheck (h : HostRow) : Bool :=
  fastFlagTensorCheck h.mask (rawFlagTensorEntries h)

theorem fastFlagTensorRowCheck_sound (h : HostRow) (hc : fastFlagTensorRowCheck h = true) :
    ∀ k, weightedCountAt (rawFlagTensorEntries h) k =
      (flagTensorKeys (maskGraph 7 h.mask)).count k := by
  simp only [fastFlagTensorRowCheck, fastFlagTensorCheck, Bool.and_eq_true_iff, List.all_eq_true,
    decide_eq_true_eq] at hc
  apply weightedCountCode_counts_of_eq (base := 8192) (fuel := 15) (by decide : 0 < 8192)
    (rawFlagTensorEntries h) (flagTensorKeys (maskGraph 7 h.mask)) hc.1.2
    (lt_of_le_of_lt (flagTensorKeys_card_le _) (by decide))
  · intro e he
    exact hc.1.1 e he
  · exact flagTensorKeys_bounded _
  · exact hc.2

end InducedPentagons.Paper

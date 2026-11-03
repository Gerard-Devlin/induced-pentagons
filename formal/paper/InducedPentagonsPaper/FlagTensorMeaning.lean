import InducedPentagonsPaper.FlagTensorPacking

/-! The upper-triangular encoding combines the two oriented off-diagonal counts. -/

namespace InducedPentagons.Paper

theorem filteredMap_count {α : Type} [DecidableEq α] (s : Finset α)
    (valid : α → Bool) (key : α → Nat) (k : Nat) :
    (((s.filter (fun x => valid x)).val).map key).count k =
      (s.filter (fun x => valid x = true ∧ key x = k)).card := by
  rw [Multiset.count_map]
  change ((s.filter (fun x => valid x)).filter (fun x => k = key x)).card = _
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hs, hv⟩, he⟩
    exact ⟨hs, hv, he.symm⟩
  · rintro ⟨hs, hv, he⟩
    exact ⟨⟨hs, hv⟩, he.symm⟩

theorem jointFlagPairCount_filter {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) :
    jointFlagPairCount hn valid classify i j =
      ((jointFlagSamples n roots free).filter (fun x => valid x.1 = true ∧
        classify x = i ∧ classify (x.swap hn) = j)).card := by
  rw [← enumeratedJointFlagPairCount_eq]
  unfold enumeratedJointFlagPairCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc]

theorem jointFlagPairKeys_count {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (block : Nat)
    (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension)
    (hd : dimension ≤ 72) (i j : Fin dimension) (hij : i.val ≤ j.val) :
    (jointFlagPairKeys hn block valid classify).count (flagTensorKey block i.val j.val) =
      if i = j then jointFlagPairCount hn valid classify i j
      else jointFlagPairCount hn valid classify i j + jointFlagPairCount hn valid classify j i := by
  classical
  let samples := jointFlagSamples n roots free
  let a := samples.filter (fun x => valid x.1 = true ∧ classify x = i ∧ classify (x.swap hn) = j)
  let b := samples.filter (fun x => valid x.1 = true ∧ classify x = j ∧ classify (x.swap hn) = i)
  have hkey (x : JointFlagSample n roots free) :
      flagTensorKey block (min (classify x).val (classify (x.swap hn)).val)
          (max (classify x).val (classify (x.swap hn)).val) = flagTensorKey block i.val j.val ↔
        (classify x = i ∧ classify (x.swap hn) = j) ∨
        (classify x = j ∧ classify (x.swap hn) = i) := by
    have hx := (classify x).isLt
    have hy := (classify (x.swap hn)).isLt
    have hi := i.isLt
    have hj := j.isLt
    constructor
    · intro he
      have heq := flagTensorKey_injective (by omega) (by omega) (by omega) (by omega) he
      simp only [Fin.ext_iff]
      omega
    · intro he
      simp only [Fin.ext_iff] at he
      unfold flagTensorKey
      omega
  unfold jointFlagPairKeys
  rw [filteredMap_count]
  change (samples.filter _).card = _
  have hf : (samples.filter (fun x => valid x.1 = true ∧
      flagTensorKey block (min (classify x).val (classify (x.swap hn)).val)
        (max (classify x).val (classify (x.swap hn)).val) = flagTensorKey block i.val j.val)) = a ∪ b := by
    ext x
    simp only [a, b, Finset.mem_filter, Finset.mem_union]
    rw [hkey]
    tauto
  rw [hf]
  by_cases he : i = j
  · subst j
    simp only [ite_true]
    change (a ∪ a).card = _
    rw [Finset.union_self]
    exact (jointFlagPairCount_filter hn valid classify i i).symm
  · rw [if_neg he]
    have hab : Disjoint a b := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      simp only [a, b, Finset.mem_filter] at hx hy
      exact he (hx.2.2.1.symm.trans hy.2.2.1)
    rw [Finset.card_union_of_disjoint hab]
    rw [jointFlagPairCount_filter, jointFlagPairCount_filter]

theorem jointFlagPairKeys_other_block {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (block other : Nat)
    (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension)
    (hd : dimension ≤ 72) (hne : block ≠ other)
    (i j : Nat) (hi : i < 72) (hj : j < 72) :
    (jointFlagPairKeys hn block valid classify).count (flagTensorKey other i j) = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hmem
  obtain ⟨x, _, he⟩ := Multiset.mem_map.mp hmem
  have hx := (classify x).isLt
  have hy := (classify (x.swap hn)).isLt
  have heq := flagTensorKey_injective (by omega) (by omega) hi hj he
  exact hne heq.1

end InducedPentagons.Paper

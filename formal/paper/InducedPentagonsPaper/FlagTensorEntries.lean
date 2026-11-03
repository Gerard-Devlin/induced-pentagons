import InducedPentagonsPaper.FlagTensorTrie

/-! The sparse tensor entries count diagonal pairs once and off-diagonal pairs twice.
The row-check hypothesis certifies every entry, including all omitted zero entries. -/

namespace InducedPentagons.Paper

theorem jointFlagPairKeys_count_upper {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (block : Nat)
    (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension)
    (hd : dimension ≤ 72) (i j : Fin dimension) (hij : i.val ≤ j.val) :
    (jointFlagPairKeys hn block valid classify).count (flagTensorKey block i.val j.val) =
      (if i = j then 1 else 2) * jointFlagPairCount hn valid classify i j := by
  rw [jointFlagPairKeys_count hn block valid classify hd i j hij]
  rw [jointFlagPairCount_symmetric hn valid classify j i]
  split <;> omega

theorem flagTensorKeys_count_one_root (g : Graph (Fin 7)) (i j : Fin 20)
    (hij : i.val ≤ j.val) :
    (flagTensorKeys g).count (flagTensorKey 0 i.val j.val) =
      (if i = j then 1 else 2) * flagProductCount_one_root g i j := by
  unfold flagTensorKeys
  simp only [Multiset.count_add]
  rw [jointFlagPairKeys_count_upper (by decide) 0 _ _ (by decide) i j hij]
  have hi : i.val < 72 := lt_of_lt_of_le i.isLt (by decide)
  have hj : j.val < 72 := lt_of_lt_of_le j.isLt (by decide)
  rw [jointFlagPairKeys_other_block (by decide) 1 0 _ _ (by decide) (by decide) _ _ hi hj,
    jointFlagPairKeys_other_block (by decide) 2 0 _ _ (by decide) (by decide) _ _ hi hj,
    jointFlagPairKeys_other_block (by decide) 3 0 _ _ (by decide) (by decide) _ _ hi hj,
    jointFlagPairKeys_other_block (by decide) 4 0 _ _ (by decide) (by decide) _ _ hi hj]
  simp only [Nat.add_zero, flagProductCount_one_root]


theorem flagTensorKeys_count_independent3 (g : Graph (Fin 7)) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    (flagTensorKeys g).count (flagTensorKey 1 i.val j.val) =
      (if i = j then 1 else 2) * flagProductCount_independent3 g i j := by
  unfold flagTensorKeys
  simp only [Multiset.count_add]
  rw [jointFlagPairKeys_count_upper (by decide) 1 _ _ (by decide) i j hij]
  rw [jointFlagPairKeys_other_block (by decide) 0 1 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 2 1 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 3 1 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 4 1 _ _ (by decide) (by decide) _ _ i.isLt j.isLt]
  simp only [Nat.add_zero, Nat.zero_add, flagProductCount_independent3]

theorem flagTensorKeys_count_edge_isolate (g : Graph (Fin 7)) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    (flagTensorKeys g).count (flagTensorKey 2 i.val j.val) =
      (if i = j then 1 else 2) * flagProductCount_edge_isolate g i j := by
  unfold flagTensorKeys
  simp only [Multiset.count_add]
  rw [jointFlagPairKeys_count_upper (by decide) 2 _ _ (by decide) i j hij]
  rw [jointFlagPairKeys_other_block (by decide) 0 2 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 1 2 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 3 2 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 4 2 _ _ (by decide) (by decide) _ _ i.isLt j.isLt]
  simp only [Nat.add_zero, Nat.zero_add, flagProductCount_edge_isolate]

theorem flagTensorKeys_count_path3 (g : Graph (Fin 7)) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    (flagTensorKeys g).count (flagTensorKey 3 i.val j.val) =
      (if i = j then 1 else 2) * flagProductCount_path3 g i j := by
  unfold flagTensorKeys
  simp only [Multiset.count_add]
  rw [jointFlagPairKeys_count_upper (by decide) 3 _ _ (by decide) i j hij]
  rw [jointFlagPairKeys_other_block (by decide) 0 3 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 1 3 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 2 3 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 4 3 _ _ (by decide) (by decide) _ _ i.isLt j.isLt]
  simp only [Nat.add_zero, Nat.zero_add, flagProductCount_path3]

theorem flagTensorKeys_count_triangle3 (g : Graph (Fin 7)) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    (flagTensorKeys g).count (flagTensorKey 4 i.val j.val) =
      (if i = j then 1 else 2) * flagProductCount_triangle3 g i j := by
  unfold flagTensorKeys
  simp only [Multiset.count_add]
  rw [jointFlagPairKeys_count_upper (by decide) 4 _ _ (by decide) i j hij]
  rw [jointFlagPairKeys_other_block (by decide) 0 4 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 1 4 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 2 4 _ _ (by decide) (by decide) _ _ i.isLt j.isLt,
    jointFlagPairKeys_other_block (by decide) 3 4 _ _ (by decide) (by decide) _ _ i.isLt j.isLt]
  simp only [Nat.add_zero, Nat.zero_add, flagProductCount_triangle3]

/-- The sum of stored counts at one sparse tensor coordinate. This remains well-defined
if a storage format contains repeated coordinates, and is zero for an omitted coordinate. -/
def rawFlagTensorCount (h : HostRow) (block i j : Nat) : Nat :=
  weightedCountAt (rawFlagTensorEntries h) (flagTensorKey block i j)

theorem weightedCountAt_eq_zero_of_absent (entries : List (Nat × Nat)) (k : Nat)
    (habsent : ∀ e ∈ entries, e.1 ≠ k) : weightedCountAt entries k = 0 := by
  induction entries with
  | nil => simp [weightedCountAt]
  | cons e es ih =>
    have he : e.1 ≠ k := habsent e (by simp)
    have hs : ∀ a ∈ es, a.1 ≠ k := fun a ha => habsent a (by simp [ha])
    simpa [weightedCountAt, he] using ih hs

theorem rawFlagTensorCount_eq_zero_of_absent (h : HostRow) (block i j : Nat)
    (habsent : ∀ e ∈ h.tensor.toList,
      flagTensorKey e.block e.i e.j ≠ flagTensorKey block i j) :
    rawFlagTensorCount h block i j = 0 := by
  apply weightedCountAt_eq_zero_of_absent
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact habsent a ha
theorem fastTrieTensorRowCheck_one_root (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 20)
    (hij : i.val ≤ j.val) :
    rawFlagTensorCount h 0 i.val j.val =
      (if i = j then 1 else 2) * flagProductCount_one_root (maskGraph 7 h.mask) i j := by
  rw [rawFlagTensorCount, fastTrieTensorRowCheck_sound h hc _ (by
    have hi := i.isLt
    have hj := j.isLt
    unfold flagTensorKey
    omega)]
  exact flagTensorKeys_count_one_root _ i j hij

theorem fastTrieTensorRowCheck_one_root_omitted (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 20)
    (hij : i.val ≤ j.val)
    (habsent : ∀ e ∈ h.tensor.toList,
      flagTensorKey e.block e.i e.j ≠ flagTensorKey 0 i.val j.val) :
    flagProductCount_one_root (maskGraph 7 h.mask) i j = 0 := by
  have hz := rawFlagTensorCount_eq_zero_of_absent h 0 i.val j.val habsent
  rw [fastTrieTensorRowCheck_one_root h hc i j hij] at hz
  split at hz <;> omega
theorem fastTrieTensorRowCheck_independent3 (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    rawFlagTensorCount h 1 i.val j.val =
      (if i = j then 1 else 2) * flagProductCount_independent3 (maskGraph 7 h.mask) i j := by
  rw [rawFlagTensorCount, fastTrieTensorRowCheck_sound h hc _ (by
    have hi := i.isLt
    have hj := j.isLt
    unfold flagTensorKey
    omega)]
  exact flagTensorKeys_count_independent3 _ i j hij

theorem fastTrieTensorRowCheck_independent3_omitted (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val)
    (habsent : ∀ e ∈ h.tensor.toList,
      flagTensorKey e.block e.i e.j ≠ flagTensorKey 1 i.val j.val) :
    flagProductCount_independent3 (maskGraph 7 h.mask) i j = 0 := by
  have hz := rawFlagTensorCount_eq_zero_of_absent h 1 i.val j.val habsent
  rw [fastTrieTensorRowCheck_independent3 h hc i j hij] at hz
  split at hz <;> omega
theorem fastTrieTensorRowCheck_edge_isolate (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    rawFlagTensorCount h 2 i.val j.val =
      (if i = j then 1 else 2) * flagProductCount_edge_isolate (maskGraph 7 h.mask) i j := by
  rw [rawFlagTensorCount, fastTrieTensorRowCheck_sound h hc _ (by
    have hi := i.isLt
    have hj := j.isLt
    unfold flagTensorKey
    omega)]
  exact flagTensorKeys_count_edge_isolate _ i j hij

theorem fastTrieTensorRowCheck_edge_isolate_omitted (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val)
    (habsent : ∀ e ∈ h.tensor.toList,
      flagTensorKey e.block e.i e.j ≠ flagTensorKey 2 i.val j.val) :
    flagProductCount_edge_isolate (maskGraph 7 h.mask) i j = 0 := by
  have hz := rawFlagTensorCount_eq_zero_of_absent h 2 i.val j.val habsent
  rw [fastTrieTensorRowCheck_edge_isolate h hc i j hij] at hz
  split at hz <;> omega
theorem fastTrieTensorRowCheck_path3 (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    rawFlagTensorCount h 3 i.val j.val =
      (if i = j then 1 else 2) * flagProductCount_path3 (maskGraph 7 h.mask) i j := by
  rw [rawFlagTensorCount, fastTrieTensorRowCheck_sound h hc _ (by
    have hi := i.isLt
    have hj := j.isLt
    unfold flagTensorKey
    omega)]
  exact flagTensorKeys_count_path3 _ i j hij

theorem fastTrieTensorRowCheck_path3_omitted (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val)
    (habsent : ∀ e ∈ h.tensor.toList,
      flagTensorKey e.block e.i e.j ≠ flagTensorKey 3 i.val j.val) :
    flagProductCount_path3 (maskGraph 7 h.mask) i j = 0 := by
  have hz := rawFlagTensorCount_eq_zero_of_absent h 3 i.val j.val habsent
  rw [fastTrieTensorRowCheck_path3 h hc i j hij] at hz
  split at hz <;> omega
theorem fastTrieTensorRowCheck_triangle3 (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val) :
    rawFlagTensorCount h 4 i.val j.val =
      (if i = j then 1 else 2) * flagProductCount_triangle3 (maskGraph 7 h.mask) i j := by
  rw [rawFlagTensorCount, fastTrieTensorRowCheck_sound h hc _ (by
    have hi := i.isLt
    have hj := j.isLt
    unfold flagTensorKey
    omega)]
  exact flagTensorKeys_count_triangle3 _ i j hij

theorem fastTrieTensorRowCheck_triangle3_omitted (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72)
    (hij : i.val ≤ j.val)
    (habsent : ∀ e ∈ h.tensor.toList,
      flagTensorKey e.block e.i e.j ≠ flagTensorKey 4 i.val j.val) :
    flagProductCount_triangle3 (maskGraph 7 h.mask) i j = 0 := by
  have hz := rawFlagTensorCount_eq_zero_of_absent h 4 i.val j.val habsent
  rw [fastTrieTensorRowCheck_triangle3 h hc i j hij] at hz
  split at hz <;> omega

end InducedPentagons.Paper


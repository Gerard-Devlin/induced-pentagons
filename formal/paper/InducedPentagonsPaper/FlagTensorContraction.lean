import InducedPentagonsPaper.FlagTensorEntries

/-! Symmetric coefficient sums agree with the upper-triangular sparse tensor convention. -/

namespace InducedPentagons.Paper

open scoped BigOperators

theorem sum_symmetric_upper_triangle {α R : Type*} [Fintype α] [LinearOrder α]
    [CommSemiring R] (f : α → α → R) (hsymm : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      ∑ i, ∑ j, if i ≤ j then (if i = j then 1 else 2) * f i j else 0 := by
  classical
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hsplit : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i = j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if j < i then f i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · subst j
      simp
    · simp [h, ne_of_gt h, not_lt_of_gt h]
  have hupper : (∑ i, ∑ j, if i ≤ j then (if i = j then 1 else 2) * f i j else 0) =
      (∑ i, ∑ j, if i = j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, le_of_lt h, ne_of_lt h, two_mul]
    · subst j
      simp
    · simp [not_le_of_gt h, ne_of_gt h, not_lt_of_gt h]
  rw [hsplit, hswap, hupper]


/-- A checked symmetric natural-number table can be contracted against any symmetric
coefficient matrix using its upper triangle and the stored doubled off-diagonal counts. -/
theorem symmetric_count_contraction {d : Nat} (counts : Fin d → Fin d → Nat)
    (stored : Fin d → Fin d → Nat) (coeff : Fin d → Fin d → ℚ)
    (hcounts : ∀ i j, counts i j = counts j i)
    (hcoeff : ∀ i j, coeff i j = coeff j i)
    (hstored : ∀ i j, i.val ≤ j.val → stored i j =
      (if i = j then 1 else 2) * counts i j) :
    (∑ i, ∑ j, if i.val ≤ j.val then (stored i j : ℚ) * coeff i j else 0) =
      ∑ i, ∑ j, (counts i j : ℚ) * coeff i j := by
  have hs : ∀ i j, (counts i j : ℚ) * coeff i j = (counts j i : ℚ) * coeff j i := by
    intro i j
    rw [hcounts i j, hcoeff i j]
  rw [sum_symmetric_upper_triangle (fun i j => (counts i j : ℚ) * coeff i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.le_iff_val_le_val]
  by_cases hle : i.val ≤ j.val
  · rw [ite_eq_left hle, ite_eq_left hle, hstored i j hle]
    push_cast
    split <;> simp [mul_assoc]
  · rw [ite_eq_right hle, ite_eq_right hle]
theorem fastTrieTensorRowCheck_one_root_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 20 → Fin 20 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 20, ∑ j : Fin 20, if i.val ≤ j.val then
      (rawFlagTensorCount h 0 i.val j.val : ℚ) * coeff i j else 0) =
      ∑ i, ∑ j, (flagProductCount_one_root (maskGraph 7 h.mask) i j : ℚ) * coeff i j := by
  apply symmetric_count_contraction
  · exact flagProductCount_one_root_symmetric _
  · exact hcoeff
  · exact fastTrieTensorRowCheck_one_root h hc
theorem fastTrieTensorRowCheck_independent3_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 1 i.val j.val : ℚ) * coeff i j else 0) =
      ∑ i, ∑ j, (flagProductCount_independent3 (maskGraph 7 h.mask) i j : ℚ) * coeff i j := by
  apply symmetric_count_contraction
  · exact flagProductCount_independent3_symmetric _
  · exact hcoeff
  · exact fastTrieTensorRowCheck_independent3 h hc
theorem fastTrieTensorRowCheck_edge_isolate_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 2 i.val j.val : ℚ) * coeff i j else 0) =
      ∑ i, ∑ j, (flagProductCount_edge_isolate (maskGraph 7 h.mask) i j : ℚ) * coeff i j := by
  apply symmetric_count_contraction
  · exact flagProductCount_edge_isolate_symmetric _
  · exact hcoeff
  · exact fastTrieTensorRowCheck_edge_isolate h hc
theorem fastTrieTensorRowCheck_path3_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 3 i.val j.val : ℚ) * coeff i j else 0) =
      ∑ i, ∑ j, (flagProductCount_path3 (maskGraph 7 h.mask) i j : ℚ) * coeff i j := by
  apply symmetric_count_contraction
  · exact flagProductCount_path3_symmetric _
  · exact hcoeff
  · exact fastTrieTensorRowCheck_path3 h hc
theorem fastTrieTensorRowCheck_triangle3_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 4 i.val j.val : ℚ) * coeff i j else 0) =
      ∑ i, ∑ j, (flagProductCount_triangle3 (maskGraph 7 h.mask) i j : ℚ) * coeff i j := by
  apply symmetric_count_contraction
  · exact flagProductCount_triangle3_symmetric _
  · exact hcoeff
  · exact fastTrieTensorRowCheck_triangle3 h hc

end InducedPentagons.Paper



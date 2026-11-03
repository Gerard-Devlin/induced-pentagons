import InducedPentagonsPaper.FlagProductDensity
import InducedPentagonsPaper.FlagTensorContraction
import InducedPentagonsPaper.FlagProductIsomorphism

/-! Normalized sparse tensor contractions and universal seven-vertex density transfer. -/

namespace InducedPentagons.Paper

open scoped BigOperators
theorem flagProductDensity_one_root_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 20) :
    flagProductDensity_one_root g i j = flagProductDensity_one_root h i j := by
  rw [flagProductDensity_one_root_eq, flagProductDensity_one_root_eq,
    flagProductCount_one_root_isomorphic e]

theorem fastTrieTensorRowCheck_one_root_normalized_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 20 → Fin 20 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 20, ∑ j : Fin 20, if i.val ≤ j.val then
      (rawFlagTensorCount h 0 i.val j.val : ℚ) / 140 * coeff i j else 0) =
      ∑ i, ∑ j, flagProductDensity_one_root (maskGraph 7 h.mask) i j * coeff i j := by
  have hs : ∀ i j, flagProductDensity_one_root (maskGraph 7 h.mask) i j * coeff i j =
      flagProductDensity_one_root (maskGraph 7 h.mask) j i * coeff j i := by
    intro i j
    rw [flagProductDensity_one_root_symmetric _ i j, hcoeff i j]
  rw [sum_symmetric_upper_triangle (fun i j =>
    flagProductDensity_one_root (maskGraph 7 h.mask) i j * coeff i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.le_iff_val_le_val]
  by_cases hij : i.val ≤ j.val
  · rw [ite_eq_left hij, ite_eq_left hij,
      fastTrieTensorRowCheck_one_root_density h hc i j hij]
    ring
  · rw [ite_eq_right hij, ite_eq_right hij]
theorem flagProductDensity_independent3_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductDensity_independent3 g i j = flagProductDensity_independent3 h i j := by
  rw [flagProductDensity_independent3_eq, flagProductDensity_independent3_eq,
    flagProductCount_independent3_isomorphic e]

theorem fastTrieTensorRowCheck_independent3_normalized_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 1 i.val j.val : ℚ) / 1260 * coeff i j else 0) =
      ∑ i, ∑ j, flagProductDensity_independent3 (maskGraph 7 h.mask) i j * coeff i j := by
  have hs : ∀ i j, flagProductDensity_independent3 (maskGraph 7 h.mask) i j * coeff i j =
      flagProductDensity_independent3 (maskGraph 7 h.mask) j i * coeff j i := by
    intro i j
    rw [flagProductDensity_independent3_symmetric _ i j, hcoeff i j]
  rw [sum_symmetric_upper_triangle (fun i j =>
    flagProductDensity_independent3 (maskGraph 7 h.mask) i j * coeff i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.le_iff_val_le_val]
  by_cases hij : i.val ≤ j.val
  · rw [ite_eq_left hij, ite_eq_left hij,
      fastTrieTensorRowCheck_independent3_density h hc i j hij]
    ring
  · rw [ite_eq_right hij, ite_eq_right hij]
theorem flagProductDensity_edge_isolate_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductDensity_edge_isolate g i j = flagProductDensity_edge_isolate h i j := by
  rw [flagProductDensity_edge_isolate_eq, flagProductDensity_edge_isolate_eq,
    flagProductCount_edge_isolate_isomorphic e]

theorem fastTrieTensorRowCheck_edge_isolate_normalized_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 2 i.val j.val : ℚ) / 1260 * coeff i j else 0) =
      ∑ i, ∑ j, flagProductDensity_edge_isolate (maskGraph 7 h.mask) i j * coeff i j := by
  have hs : ∀ i j, flagProductDensity_edge_isolate (maskGraph 7 h.mask) i j * coeff i j =
      flagProductDensity_edge_isolate (maskGraph 7 h.mask) j i * coeff j i := by
    intro i j
    rw [flagProductDensity_edge_isolate_symmetric _ i j, hcoeff i j]
  rw [sum_symmetric_upper_triangle (fun i j =>
    flagProductDensity_edge_isolate (maskGraph 7 h.mask) i j * coeff i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.le_iff_val_le_val]
  by_cases hij : i.val ≤ j.val
  · rw [ite_eq_left hij, ite_eq_left hij,
      fastTrieTensorRowCheck_edge_isolate_density h hc i j hij]
    ring
  · rw [ite_eq_right hij, ite_eq_right hij]
theorem flagProductDensity_path3_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductDensity_path3 g i j = flagProductDensity_path3 h i j := by
  rw [flagProductDensity_path3_eq, flagProductDensity_path3_eq,
    flagProductCount_path3_isomorphic e]

theorem fastTrieTensorRowCheck_path3_normalized_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 3 i.val j.val : ℚ) / 1260 * coeff i j else 0) =
      ∑ i, ∑ j, flagProductDensity_path3 (maskGraph 7 h.mask) i j * coeff i j := by
  have hs : ∀ i j, flagProductDensity_path3 (maskGraph 7 h.mask) i j * coeff i j =
      flagProductDensity_path3 (maskGraph 7 h.mask) j i * coeff j i := by
    intro i j
    rw [flagProductDensity_path3_symmetric _ i j, hcoeff i j]
  rw [sum_symmetric_upper_triangle (fun i j =>
    flagProductDensity_path3 (maskGraph 7 h.mask) i j * coeff i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.le_iff_val_le_val]
  by_cases hij : i.val ≤ j.val
  · rw [ite_eq_left hij, ite_eq_left hij,
      fastTrieTensorRowCheck_path3_density h hc i j hij]
    ring
  · rw [ite_eq_right hij, ite_eq_right hij]
theorem flagProductDensity_triangle3_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductDensity_triangle3 g i j = flagProductDensity_triangle3 h i j := by
  rw [flagProductDensity_triangle3_eq, flagProductDensity_triangle3_eq,
    flagProductCount_triangle3_isomorphic e]

theorem fastTrieTensorRowCheck_triangle3_normalized_contraction (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (coeff : Fin 72 → Fin 72 → ℚ)
    (hcoeff : ∀ i j, coeff i j = coeff j i) :
    (∑ i : Fin 72, ∑ j : Fin 72, if i.val ≤ j.val then
      (rawFlagTensorCount h 4 i.val j.val : ℚ) / 1260 * coeff i j else 0) =
      ∑ i, ∑ j, flagProductDensity_triangle3 (maskGraph 7 h.mask) i j * coeff i j := by
  have hs : ∀ i j, flagProductDensity_triangle3 (maskGraph 7 h.mask) i j * coeff i j =
      flagProductDensity_triangle3 (maskGraph 7 h.mask) j i * coeff j i := by
    intro i j
    rw [flagProductDensity_triangle3_symmetric _ i j, hcoeff i j]
  rw [sum_symmetric_upper_triangle (fun i j =>
    flagProductDensity_triangle3 (maskGraph 7 h.mask) i j * coeff i j) hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.le_iff_val_le_val]
  by_cases hij : i.val ≤ j.val
  · rw [ite_eq_left hij, ite_eq_left hij,
      fastTrieTensorRowCheck_triangle3_density h hc i j hij]
    ring
  · rw [ite_eq_right hij, ite_eq_right hij]
theorem flagProductDensities_reduced_to_certificate (g : Graph (Fin 7)) :
    ∃ m ∈ Generated.certificate.hosts.toList,
      (∀ i j, flagProductDensity_one_root g i j =
        flagProductDensity_one_root (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductDensity_independent3 g i j =
        flagProductDensity_independent3 (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductDensity_edge_isolate g i j =
        flagProductDensity_edge_isolate (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductDensity_path3 g i j =
        flagProductDensity_path3 (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductDensity_triangle3 g i j =
        flagProductDensity_triangle3 (maskGraph 7 m) i j) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := atlas7_covers g
  refine ⟨m, ?_, flagProductDensity_one_root_isomorphic e,
    flagProductDensity_independent3_isomorphic e, flagProductDensity_edge_isolate_isomorphic e,
    flagProductDensity_path3_isomorphic e, flagProductDensity_triangle3_isomorphic e⟩
  rwa [← atlas7_eq_certificate_hosts]

end InducedPentagons.Paper

import InducedPentagonsPaper.FlagTensorEntries

/-! Exact normalization of flag-product counts by the full finite joint-sample space. -/

namespace InducedPentagons.Paper

noncomputable def jointFlagPairDensity {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) : ℚ :=
  (jointFlagPairCount hn valid classify i j : ℚ) /
    (n.descFactorial roots * (n - roots).choose free : Nat)

theorem jointFlagPairDensity_nonneg {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) :
    0 ≤ jointFlagPairDensity hn valid classify i j := by
  unfold jointFlagPairDensity
  positivity

theorem jointFlagPairDensity_le_one {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) :
    jointFlagPairDensity hn valid classify i j ≤ 1 := by
  unfold jointFlagPairDensity
  apply div_le_one_of_le₀
  · exact_mod_cast jointFlagPairCount_le hn valid classify i j
  · positivity

theorem jointFlagPairDensity_symmetric {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) :
    jointFlagPairDensity hn valid classify i j = jointFlagPairDensity hn valid classify j i := by
  unfold jointFlagPairDensity
  rw [jointFlagPairCount_symmetric hn valid classify i j]


noncomputable def flagProductDensity_one_root (g : Graph (Fin 7))
    (i j : Fin 20) : ℚ :=
  jointFlagPairDensity (n := 7) (roots := 1) (free := 3) (by decide)
    (jointRootCheck (free := 3) 0 g) (fun x => indexedFlag_one_root (x.graph g)) i j

theorem flagProductDensity_one_root_eq (g : Graph (Fin 7)) (i j : Fin 20) :
    flagProductDensity_one_root g i j = (flagProductCount_one_root g i j : ℚ) / 140 := by
  rfl

theorem flagProductDensity_one_root_nonneg (g : Graph (Fin 7)) (i j : Fin 20) :
    0 ≤ flagProductDensity_one_root g i j :=
  jointFlagPairDensity_nonneg _ _ _ i j

theorem flagProductDensity_one_root_le_one (g : Graph (Fin 7)) (i j : Fin 20) :
    flagProductDensity_one_root g i j ≤ 1 :=
  jointFlagPairDensity_le_one _ _ _ i j

theorem flagProductDensity_one_root_symmetric (g : Graph (Fin 7)) (i j : Fin 20) :
    flagProductDensity_one_root g i j = flagProductDensity_one_root g j i :=
  jointFlagPairDensity_symmetric _ _ _ i j

theorem flagProductDensity_one_root_certificate_denominator (g : Graph (Fin 7))
    (i j : Fin 20) :
    flagProductDensity_one_root g i j = (flagProductCount_one_root g i j : ℚ) /
      ((Generated.certificate.blocks[0]!).denominator : ℚ) := by
  rw [flagProductDenominator_one_root, jointFlagSample_one_root_card]
  exact flagProductDensity_one_root_eq g i j

theorem fastTrieTensorRowCheck_one_root_density (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 20) (hij : i.val ≤ j.val) :
    (rawFlagTensorCount h 0 i.val j.val : ℚ) / 140 =
      (if i = j then 1 else 2) * flagProductDensity_one_root (maskGraph 7 h.mask) i j := by
  rw [fastTrieTensorRowCheck_one_root h hc i j hij, flagProductDensity_one_root_eq]
  push_cast
  split <;> ring
noncomputable def flagProductDensity_independent3 (g : Graph (Fin 7))
    (i j : Fin 72) : ℚ :=
  jointFlagPairDensity (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 0 g) (fun x => indexedFlag_independent3 (x.graph g)) i j

theorem flagProductDensity_independent3_eq (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_independent3 g i j = (flagProductCount_independent3 g i j : ℚ) / 1260 := by
  rfl

theorem flagProductDensity_independent3_nonneg (g : Graph (Fin 7)) (i j : Fin 72) :
    0 ≤ flagProductDensity_independent3 g i j :=
  jointFlagPairDensity_nonneg _ _ _ i j

theorem flagProductDensity_independent3_le_one (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_independent3 g i j ≤ 1 :=
  jointFlagPairDensity_le_one _ _ _ i j

theorem flagProductDensity_independent3_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_independent3 g i j = flagProductDensity_independent3 g j i :=
  jointFlagPairDensity_symmetric _ _ _ i j

theorem flagProductDensity_independent3_certificate_denominator (g : Graph (Fin 7))
    (i j : Fin 72) :
    flagProductDensity_independent3 g i j = (flagProductCount_independent3 g i j : ℚ) /
      ((Generated.certificate.blocks[1]!).denominator : ℚ) := by
  rw [flagProductDenominator_independent3, jointFlagSample_three_roots_card]
  exact flagProductDensity_independent3_eq g i j

theorem fastTrieTensorRowCheck_independent3_density (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72) (hij : i.val ≤ j.val) :
    (rawFlagTensorCount h 1 i.val j.val : ℚ) / 1260 =
      (if i = j then 1 else 2) * flagProductDensity_independent3 (maskGraph 7 h.mask) i j := by
  rw [fastTrieTensorRowCheck_independent3 h hc i j hij, flagProductDensity_independent3_eq]
  push_cast
  split <;> ring
noncomputable def flagProductDensity_edge_isolate (g : Graph (Fin 7))
    (i j : Fin 72) : ℚ :=
  jointFlagPairDensity (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 1 g) (fun x => indexedFlag_edge_isolate (x.graph g)) i j

theorem flagProductDensity_edge_isolate_eq (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_edge_isolate g i j = (flagProductCount_edge_isolate g i j : ℚ) / 1260 := by
  rfl

theorem flagProductDensity_edge_isolate_nonneg (g : Graph (Fin 7)) (i j : Fin 72) :
    0 ≤ flagProductDensity_edge_isolate g i j :=
  jointFlagPairDensity_nonneg _ _ _ i j

theorem flagProductDensity_edge_isolate_le_one (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_edge_isolate g i j ≤ 1 :=
  jointFlagPairDensity_le_one _ _ _ i j

theorem flagProductDensity_edge_isolate_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_edge_isolate g i j = flagProductDensity_edge_isolate g j i :=
  jointFlagPairDensity_symmetric _ _ _ i j

theorem flagProductDensity_edge_isolate_certificate_denominator (g : Graph (Fin 7))
    (i j : Fin 72) :
    flagProductDensity_edge_isolate g i j = (flagProductCount_edge_isolate g i j : ℚ) /
      ((Generated.certificate.blocks[2]!).denominator : ℚ) := by
  rw [flagProductDenominator_edge_isolate, jointFlagSample_three_roots_card]
  exact flagProductDensity_edge_isolate_eq g i j

theorem fastTrieTensorRowCheck_edge_isolate_density (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72) (hij : i.val ≤ j.val) :
    (rawFlagTensorCount h 2 i.val j.val : ℚ) / 1260 =
      (if i = j then 1 else 2) * flagProductDensity_edge_isolate (maskGraph 7 h.mask) i j := by
  rw [fastTrieTensorRowCheck_edge_isolate h hc i j hij, flagProductDensity_edge_isolate_eq]
  push_cast
  split <;> ring
noncomputable def flagProductDensity_path3 (g : Graph (Fin 7))
    (i j : Fin 72) : ℚ :=
  jointFlagPairDensity (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 17 g) (fun x => indexedFlag_path3 (x.graph g)) i j

theorem flagProductDensity_path3_eq (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_path3 g i j = (flagProductCount_path3 g i j : ℚ) / 1260 := by
  rfl

theorem flagProductDensity_path3_nonneg (g : Graph (Fin 7)) (i j : Fin 72) :
    0 ≤ flagProductDensity_path3 g i j :=
  jointFlagPairDensity_nonneg _ _ _ i j

theorem flagProductDensity_path3_le_one (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_path3 g i j ≤ 1 :=
  jointFlagPairDensity_le_one _ _ _ i j

theorem flagProductDensity_path3_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_path3 g i j = flagProductDensity_path3 g j i :=
  jointFlagPairDensity_symmetric _ _ _ i j

theorem flagProductDensity_path3_certificate_denominator (g : Graph (Fin 7))
    (i j : Fin 72) :
    flagProductDensity_path3 g i j = (flagProductCount_path3 g i j : ℚ) /
      ((Generated.certificate.blocks[3]!).denominator : ℚ) := by
  rw [flagProductDenominator_path3, jointFlagSample_three_roots_card]
  exact flagProductDensity_path3_eq g i j

theorem fastTrieTensorRowCheck_path3_density (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72) (hij : i.val ≤ j.val) :
    (rawFlagTensorCount h 3 i.val j.val : ℚ) / 1260 =
      (if i = j then 1 else 2) * flagProductDensity_path3 (maskGraph 7 h.mask) i j := by
  rw [fastTrieTensorRowCheck_path3 h hc i j hij, flagProductDensity_path3_eq]
  push_cast
  split <;> ring
noncomputable def flagProductDensity_triangle3 (g : Graph (Fin 7))
    (i j : Fin 72) : ℚ :=
  jointFlagPairDensity (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 19 g) (fun x => indexedFlag_triangle3 (x.graph g)) i j

theorem flagProductDensity_triangle3_eq (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_triangle3 g i j = (flagProductCount_triangle3 g i j : ℚ) / 1260 := by
  rfl

theorem flagProductDensity_triangle3_nonneg (g : Graph (Fin 7)) (i j : Fin 72) :
    0 ≤ flagProductDensity_triangle3 g i j :=
  jointFlagPairDensity_nonneg _ _ _ i j

theorem flagProductDensity_triangle3_le_one (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_triangle3 g i j ≤ 1 :=
  jointFlagPairDensity_le_one _ _ _ i j

theorem flagProductDensity_triangle3_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductDensity_triangle3 g i j = flagProductDensity_triangle3 g j i :=
  jointFlagPairDensity_symmetric _ _ _ i j

theorem flagProductDensity_triangle3_certificate_denominator (g : Graph (Fin 7))
    (i j : Fin 72) :
    flagProductDensity_triangle3 g i j = (flagProductCount_triangle3 g i j : ℚ) /
      ((Generated.certificate.blocks[4]!).denominator : ℚ) := by
  rw [flagProductDenominator_triangle3, jointFlagSample_three_roots_card]
  exact flagProductDensity_triangle3_eq g i j

theorem fastTrieTensorRowCheck_triangle3_density (h : HostRow)
    (hc : fastTrieTensorRowCheck h = true) (i j : Fin 72) (hij : i.val ≤ j.val) :
    (rawFlagTensorCount h 4 i.val j.val : ℚ) / 1260 =
      (if i = j then 1 else 2) * flagProductDensity_triangle3 (maskGraph 7 h.mask) i j := by
  rw [fastTrieTensorRowCheck_triangle3 h hc i j hij, flagProductDensity_triangle3_eq]
  push_cast
  split <;> ring

end InducedPentagons.Paper


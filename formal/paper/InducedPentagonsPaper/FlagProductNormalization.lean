import InducedPentagonsPaper.FlagProductSemantics

/-! Flag-pair counts partition the samples whose ordered roots have the required type. -/

namespace InducedPentagons.Paper

open scoped BigOperators

def jointFlagPairPartitionEquiv {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) :
    (Σ i : Fin dimension, Σ j : Fin dimension,
      {x : JointFlagSample n roots free // valid x.1 = true ∧ classify x = i ∧
        classify (x.swap hn) = j}) ≃
      {x : JointFlagSample n roots free // valid x.1 = true} where
  toFun y := ⟨y.2.2.val, y.2.2.property.1⟩
  invFun x := ⟨classify x.val, classify (x.val.swap hn), x.val, x.property, rfl, rfl⟩
  left_inv y := by
    rcases y with ⟨i, j, x, hv, hi, hj⟩
    subst i
    subst j
    rfl
  right_inv x := rfl

theorem jointFlagPairCount_sum {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) :
    (∑ i, ∑ j, jointFlagPairCount hn valid classify i j) =
      Nat.card {x : JointFlagSample n roots free // valid x.1 = true} := by
  classical
  have he := Fintype.card_congr (jointFlagPairPartitionEquiv hn valid classify)
  simpa only [Fintype.card_sigma, jointFlagPairCount, Nat.card_eq_fintype_card] using he

theorem jointFlagPairCount_sum_le {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) :
    (∑ i, ∑ j, jointFlagPairCount hn valid classify i j) ≤
      n.descFactorial roots * (n - roots).choose free := by
  classical
  rw [jointFlagPairCount_sum, Nat.card_eq_fintype_card, ← jointFlagSample_card]
  exact Fintype.card_subtype_le _

def jointFlagValidRootsEquiv {n roots free : Nat}
    (valid : (Fin roots ↪ Fin n) → Bool) :
    {x : JointFlagSample n roots free // valid x.1 = true} ≃
      (Σ f : {f : Fin roots ↪ Fin n // valid f = true},
        {s : Finset (Fin n) // s ⊆ (flagRootVertices f.val)ᶜ ∧ s.card = free}) where
  toFun x := ⟨⟨x.val.1, x.property⟩, x.val.2⟩
  invFun y := ⟨⟨y.1.val, y.2⟩, y.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each valid ordered root injection has the same number of left-extension choices. -/
theorem jointFlagPairCount_sum_eq_rootCount {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) :
    (∑ i, ∑ j, jointFlagPairCount hn valid classify i j) =
      Nat.card {f : Fin roots ↪ Fin n // valid f = true} * (n - roots).choose free := by
  classical
  rw [jointFlagPairCount_sum, Nat.card_congr (jointFlagValidRootsEquiv valid),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [jointFlag_left_choice_card, Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul, Nat.card_eq_fintype_card]
theorem jointRootCheck_one_root (g : Graph (Fin 7)) (f : Fin 1 ↪ Fin 7) :
    jointRootCheck (free := 3) 0 g f = true := by
  simp only [jointRootCheck, decide_eq_true_eq]
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  rw [g.loopless, (maskGraph 4 0).loopless]

theorem flagProductCount_one_root_sum (g : Graph (Fin 7)) :
    (∑ i, ∑ j, flagProductCount_one_root g i j) = 140 := by
  classical
  unfold flagProductCount_one_root
  rw [jointFlagPairCount_sum]
  have he : {x : JointFlagSample 7 1 3 // jointRootCheck (free := 3) 0 g x.1 = true} ≃
      JointFlagSample 7 1 3 := Equiv.subtypeUnivEquiv (fun x => jointRootCheck_one_root g x.1)
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, jointFlagSample_one_root_card]


theorem flagProductCount_independent3_sum_le (g : Graph (Fin 7)) :
    (∑ i, ∑ j, flagProductCount_independent3 g i j) ≤ 1260 :=
  jointFlagPairCount_sum_le (by decide) _ _

theorem flagProductCount_edge_isolate_sum_le (g : Graph (Fin 7)) :
    (∑ i, ∑ j, flagProductCount_edge_isolate g i j) ≤ 1260 :=
  jointFlagPairCount_sum_le (by decide) _ _

theorem flagProductCount_path3_sum_le (g : Graph (Fin 7)) :
    (∑ i, ∑ j, flagProductCount_path3 g i j) ≤ 1260 :=
  jointFlagPairCount_sum_le (by decide) _ _

theorem flagProductCount_triangle3_sum_le (g : Graph (Fin 7)) :
    (∑ i, ∑ j, flagProductCount_triangle3 g i j) ≤ 1260 :=
  jointFlagPairCount_sum_le (by decide) _ _

/-- The unconditional one-root flag-product probabilities sum to one. -/
theorem flagProductProbability_one_root_sum (g : Graph (Fin 7)) :
    (∑ i, ∑ j, (flagProductCount_one_root g i j : ℚ) / 140) = 1 := by
  simp only [← Finset.sum_div, ← Nat.cast_sum]
  rw [flagProductCount_one_root_sum]
  norm_num

end InducedPentagons.Paper
import InducedPentagonsPaper.FlagProductNormalization
import InducedPentagonsPaper.JointFlagPermutation

namespace InducedPentagons.Paper

open scoped BigOperators

/-- Contracting the joint-count table is exactly a uniform sum over valid samples. -/
theorem jointFlagPairCount_contraction {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension)
    (coeff : Fin dimension → Fin dimension → ℚ) :
    (∑ i, ∑ j, (jointFlagPairCount hn valid classify i j : ℚ) * coeff i j) =
      ∑ x : {x : JointFlagSample n roots free // valid x.1 = true},
        coeff (classify x.val) (classify (x.val.swap hn)) := by
  classical
  have he := Fintype.sum_equiv (jointFlagPairPartitionEquiv hn valid classify)
    (fun y => coeff y.1 y.2.1)
    (fun x => coeff (classify x.val) (classify (x.val.swap hn))) (by
      intro y
      change coeff y.1 y.2.1 = coeff (classify y.2.2.val) (classify (y.2.2.val.swap hn))
      rw [y.2.2.property.2.1, y.2.2.property.2.2])
  simpa only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    jointFlagPairCount] using he

/-- A contraction of a nonnegative coefficient table is nonnegative. -/
theorem jointFlagPairCount_contraction_nonnegative {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension)
    (coeff : Fin dimension → Fin dimension → ℚ) (hcoeff : ∀ i j, 0 ≤ coeff i j) :
    0 ≤ (∑ i, ∑ j, (jointFlagPairCount hn valid classify i j : ℚ) * coeff i j) := by
  rw [jointFlagPairCount_contraction]
  exact Finset.sum_nonneg (fun x _ => hcoeff _ _)
/-- Any sample statistic has the same expectation under a uniform permutation. -/
theorem jointFlagFullPermutation_sum {n roots free : Nat}
    (hn : n = roots + 2 * free) (f : JointFlagSample n roots free → ℚ) :
    (∑ e : Equiv.Perm (Fin n), f (jointFlagSampleOfPermutation hn e)) =
      (free.factorial ^ 2 : ℚ) * ∑ x : JointFlagSample n roots free, f x := by
  classical
  let E := Equiv.sigmaFiberEquiv (jointFlagSampleOfPermutation hn)
  have he := Fintype.sum_equiv E
    (fun y => f y.1) (fun e => f (jointFlagSampleOfPermutation hn e)) (by
      intro y
      change f y.1 = f (jointFlagSampleOfPermutation hn y.2.val)
      rw [y.2.property])
  rw [← he, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [← Nat.card_eq_fintype_card, jointFlagFullPermutation_fiber_card hn]
  push_cast
  rw [Finset.mul_sum]

theorem jointFlagFullPermutation_expectation {n roots free : Nat}
    (hn : n = roots + 2 * free) (f : JointFlagSample n roots free → ℚ) :
    (∑ e : Equiv.Perm (Fin n), f (jointFlagSampleOfPermutation hn e)) / n.factorial =
      (∑ x : JointFlagSample n roots free, f x) /
        (n.descFactorial roots * (n - roots).choose free) := by
  rw [jointFlagFullPermutation_sum hn, ← jointFlagSample_card_mul_factorial_sq hn]
  push_cast
  rw [mul_comm ((free.factorial : ℚ) ^ 2)]
  exact mul_div_mul_right _ _ (by positivity)


/-- The one-root table contraction is a sample average with the actual denominator 140. -/
theorem flagProduct_one_root_expectation (g : Graph (Fin 7)) (coeff : Fin 20 → Fin 20 → ℚ) :
    (∑ i, ∑ j, (flagProductCount_one_root g i j : ℚ) * coeff i j) / 140 =
      (∑ x : JointFlagSample 7 1 3,
        coeff (indexedFlag_one_root (x.graph g))
          (indexedFlag_one_root ((x.swap (by decide)).graph g))) / 140 := by
  unfold flagProductCount_one_root
  rw [jointFlagPairCount_contraction]
  congr 1
  classical
  let E := Equiv.subtypeUnivEquiv (fun x : JointFlagSample 7 1 3 => jointRootCheck_one_root g x.1)
  apply Fintype.sum_equiv E
  intro x
  rfl

/-- The one-root table also contracts to the uniform average over all 7! permutations. -/
theorem flagProduct_one_root_permutation_expectation (g : Graph (Fin 7))
    (coeff : Fin 20 → Fin 20 → ℚ) :
    (∑ i, ∑ j, (flagProductCount_one_root g i j : ℚ) * coeff i j) / 140 =
      (∑ e : Equiv.Perm (Fin 7),
        let x := jointFlagSampleOfPermutation (n := 7) (roots := 1) (free := 3) (by decide) e
        coeff (indexedFlag_one_root (x.graph g))
          (indexedFlag_one_root ((x.swap (by decide)).graph g))) / 5040 := by
  rw [flagProduct_one_root_expectation]
  convert (jointFlagFullPermutation_expectation (n := 7) (roots := 1) (free := 3)
    (by decide) (fun x => coeff (indexedFlag_one_root (x.graph g))
      (indexedFlag_one_root ((x.swap (by decide)).graph g)))).symm using 1 <;> norm_num [Nat.choose]

end InducedPentagons.Paper
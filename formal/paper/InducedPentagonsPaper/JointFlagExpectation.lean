import InducedPentagonsPaper.JointFlagPermutation

/-! Uniform permutation sampling transports arbitrary finite sums and rational averages
of joint flag statistics, including coefficient matrices evaluated on sampled flag pairs. -/

namespace InducedPentagons.Paper

open scoped BigOperators

/-- Every joint sample contributes exactly `(free!)²` times to a full permutation sum. -/
theorem jointFlagFullPermutation_sum {n roots free : Nat} {R : Type*} [CommSemiring R]
    (hn : n = roots + 2 * free) (f : JointFlagSample n roots free → R) :
    (∑ e : Equiv.Perm (Fin n), f (jointFlagSampleOfPermutation hn e)) =
      (free.factorial ^ 2 : R) * ∑ x, f x := by
  classical
  rw [← Fintype.sum_fiberwise' (jointFlagSampleOfPermutation hn) f]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    jointFlagFullPermutation_fiber_card hn, nsmul_eq_mul]
  simp only [Nat.cast_pow, ← Finset.mul_sum]

/-- Forgetting the internal ordering of the free blocks preserves every rational average. -/
theorem jointFlagFullPermutation_average {n roots free : Nat}
    (hn : n = roots + 2 * free) (f : JointFlagSample n roots free → ℚ) :
    (∑ e : Equiv.Perm (Fin n), f (jointFlagSampleOfPermutation hn e)) / n.factorial =
      (∑ x, f x) / (n.descFactorial roots * (n - roots).choose free : Nat) := by
  rw [jointFlagFullPermutation_sum hn, ← jointFlagSample_card_mul_factorial_sq hn]
  push_cast
  rw [mul_comm ((free.factorial : ℚ) ^ 2)]
  exact mul_div_mul_right _ _ (by positivity)

/-- The normalization of every one-root rational statistic is 140 unordered samples. -/
theorem jointFlagFullPermutation_one_root_average (f : JointFlagSample 7 1 3 → ℚ) :
    (∑ e : Equiv.Perm (Fin 7), f (jointFlagSampleOfPermutation (by decide) e)) / 5040 =
      (∑ x, f x) / 140 := by
  exact jointFlagFullPermutation_average (by decide) f

/-- The normalization of every three-root rational statistic is 1260 unordered samples. -/
theorem jointFlagFullPermutation_three_roots_average (f : JointFlagSample 7 3 2 → ℚ) :
    (∑ e : Equiv.Perm (Fin 7), f (jointFlagSampleOfPermutation (by decide) e)) / 5040 =
      (∑ x, f x) / 1260 := by
  exact jointFlagFullPermutation_average (by decide) f

end InducedPentagons.Paper

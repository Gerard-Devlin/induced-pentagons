import InducedPentagonsPaper.SharpConstruction

/-! Zero-edge boundary cases and equivalent forms of the sharp inequality. -/

open scoped BigOperators

noncomputable section

namespace InducedPentagons.Paper

variable {V : Type} [Fintype V]

/-- With nonnegative weights, zero edge mass forces every edge product to vanish. -/
theorem dart_weight_eq_zero_of_edgeMass_eq_zero (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hE : edgeMass g x = 0) (p : Darts g) :
    x p.val.1 * x p.val.2 = 0 := by
  have hsum : (∑ q : Darts g, x q.val.1 * x q.val.2) = 0 := by
    simpa [edgeMass] using hE
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => mul_nonneg (hx q.val.1) (hx q.val.2))).mp hsum p (Finset.mem_univ p)

/-- Every pentagon contains an edge, so it has zero weight when all edge
products vanish. -/
theorem pentagonMass_eq_zero_of_edgeMass_eq_zero (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hE : edgeMass g x = 0) : pentagonMass g x = 0 := by
  unfold pentagonMass
  have hsum : (∑ p : PentagonEmbedding g, ∏ i, x (p.val i)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hedge : g.adj (p.val 0) (p.val 1) = true := by
      simpa [cycleAdj] using p.property 0 1
    have hprod := dart_weight_eq_zero_of_edgeMass_eq_zero g hx hE
      (⟨(p.val 0, p.val 1), hedge⟩ : Darts g)
    change x (p.val 0) * x (p.val 1) = 0 at hprod
    rcases mul_eq_zero.mp hprod with h | h
    · exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 5)) h
    · exact Finset.prod_eq_zero (Finset.mem_univ (1 : Fin 5)) h
  rw [hsum, zero_div]

/-- The squared sharp inequality and the square-root form are equivalent,
including at zero edge mass. -/
theorem sharp_bound_iff_squared (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) :
    (pentagonMass g x ≤ sharpConstant * edgeMass g x ^ 2 * Real.sqrt (edgeMass g x)) ↔
    (pentagonMass g x ^ 2 ≤ (9 / 25000 : ℝ) * edgeMass g x ^ 5) := by
  have hE := edgeMass_nonnegative g hx
  have hP := pentagonMass_nonnegative g hx
  have hR : 0 ≤ sharpConstant * edgeMass g x ^ 2 * Real.sqrt (edgeMass g x) :=
    mul_nonneg (mul_nonneg sharpConstant_positive.le (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hs : (sharpConstant * edgeMass g x ^ 2 * Real.sqrt (edgeMass g x)) ^ 2 =
      (9 / 25000 : ℝ) * edgeMass g x ^ 5 := by
    rw [mul_pow, mul_pow, sharpConstant_sq, Real.sq_sqrt hE]
    ring
  rw [← hs]
  exact (sq_le_sq₀ hP hR).symm

theorem edgeMass_pos_of_pentagonMass_pos (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hP : 0 < pentagonMass g x) : 0 < edgeMass g x := by
  apply lt_of_le_of_ne (edgeMass_nonnegative g hx)
  intro hE
  have hzero := pentagonMass_eq_zero_of_edgeMass_eq_zero g hx hE.symm
  exact (ne_of_gt hP) hzero

/-- On the positive-edge locus the normalized squared ratio expresses exactly
the same sharp bound. -/
theorem sharp_bound_iff_squaredRatio (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hE : 0 < edgeMass g x) :
    (pentagonMass g x ≤ sharpConstant * edgeMass g x ^ 2 * Real.sqrt (edgeMass g x)) ↔
    squaredRatio g x ≤ (9 / 25000 : ℝ) := by
  rw [sharp_bound_iff_squared g hx]
  unfold squaredRatio
  exact (div_le_iff₀ (pow_pos hE 5)).symm
end InducedPentagons.Paper

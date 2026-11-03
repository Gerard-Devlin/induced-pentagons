import InducedPentagonsPaper.WeightedGraphLimits

/-! Reduction of homogeneous weighted bounds to the unit-mass simplex. -/

open scoped BigOperators

noncomputable section

namespace InducedPentagons.Paper

variable {V : Type} [Fintype V]

def normalizedWeights (x : V → ℝ) (v : V) : ℝ :=
  (∑ u, x u)⁻¹ * x v

theorem weights_eq_zero_of_sum_eq_zero {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hs : ∑ v, x v = 0) : x = 0 := by
  funext v
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hx u)).mp hs v (Finset.mem_univ v)

theorem normalizedWeights_mem_unitMass {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hs : 0 < ∑ v, x v) :
    normalizedWeights x ∈ unitMassWeights V := by
  constructor
  · intro v
    exact mul_nonneg (inv_nonneg.mpr hs.le) (hx v)
  · simp only [normalizedWeights, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']

theorem edgeMass_normalizedWeights (g : Graph V) (x : V → ℝ) :
    edgeMass g (normalizedWeights x) = (∑ v, x v)⁻¹ ^ 2 * edgeMass g x :=
  edgeMass_scale g x (∑ v, x v)⁻¹

theorem pentagonMass_normalizedWeights (g : Graph V) (x : V → ℝ) :
    pentagonMass g (normalizedWeights x) = (∑ v, x v)⁻¹ ^ 5 * pentagonMass g x :=
  pentagonMass_scale g x (∑ v, x v)⁻¹

theorem squaredRatio_normalizedWeights (g : Graph V) (x : V → ℝ)
    (hs : ∑ v, x v ≠ 0) : squaredRatio g (normalizedWeights x) = squaredRatio g x :=
  squaredRatio_scale g x (inv_ne_zero hs)

/-- The squared pentagon inequality for unit total mass suffices for all
nonnegative weights, including the zero vector and empty vertex types. -/
theorem squared_pentagon_bound_of_unitMass (g : Graph V) (c : ℝ)
    (hunit : ∀ y ∈ unitMassWeights V, pentagonMass g y ^ 2 ≤ c * edgeMass g y ^ 5)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    pentagonMass g x ^ 2 ≤ c * edgeMass g x ^ 5 := by
  have hsnonneg : 0 ≤ ∑ v, x v := Finset.sum_nonneg (fun v _ => hx v)
  rcases eq_or_lt_of_le hsnonneg with hs | hs
  · have hx0 := weights_eq_zero_of_sum_eq_zero hx hs.symm
    subst x
    simp [pentagonMass, edgeMass]
  · have h := hunit (normalizedWeights x) (normalizedWeights_mem_unitMass hx hs)
    rw [pentagonMass_normalizedWeights, edgeMass_normalizedWeights] at h
    have hscale : (∑ v, x v)⁻¹ ^ 10 * pentagonMass g x ^ 2 ≤
        (∑ v, x v)⁻¹ ^ 10 * (c * edgeMass g x ^ 5) := by
      convert h using 1 <;> ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < (∑ v, x v)⁻¹ ^ 10)).mp hscale

theorem squared_pentagon_bound_unitMass_iff (g : Graph V) (c : ℝ) :
    (∀ y ∈ unitMassWeights V, pentagonMass g y ^ 2 ≤ c * edgeMass g y ^ 5) ↔
    (∀ x : V → ℝ, (∀ v, 0 ≤ x v) →
      pentagonMass g x ^ 2 ≤ c * edgeMass g x ^ 5) := by
  constructor
  · intro h x hx
    exact squared_pentagon_bound_of_unitMass g c h hx
  · intro h y hy
    exact h y hy.1

end InducedPentagons.Paper

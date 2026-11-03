import InducedPentagonsPaper.WeightedGraphLimits
import Mathlib.Analysis.SpecificLimits.Basic

/-! Rounded nonnegative weights and transfer of the homogeneous squared
pentagon inequality from integral weights to real weights. This is a reduction:
the integral inequality remains an explicit hypothesis, not an assumed axiom. -/

open scoped BigOperators Topology
open Filter

noncomputable section

namespace InducedPentagons.Paper

variable {V : Type}

/-- Integral weights rescaled by the mesh size. The zero mesh is harmless. -/
def roundedWeights (x : V → ℝ) (n : ℕ) (v : V) : ℝ :=
  (n : ℝ)⁻¹ * (⌊x v * (n : ℝ)⌋₊ : ℝ)

theorem roundedWeights_nonnegative (x : V → ℝ) (n : ℕ) (v : V) :
    0 ≤ roundedWeights x n v := by
  unfold roundedWeights
  positivity

theorem tendsto_roundedWeights {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) (v : V) :
    Tendsto (fun n => roundedWeights x n v) atTop (𝓝 (x v)) := by
  simpa only [Function.comp_def, roundedWeights, div_eq_mul_inv, mul_comm] using
    (tendsto_nat_floor_mul_div_atTop (hx v)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

variable [Fintype V]

theorem tendsto_edgeMass_roundedWeights (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) :
    Tendsto (fun n => edgeMass g (roundedWeights x n)) atTop (𝓝 (edgeMass g x)) :=
  tendsto_edgeMass g (tendsto_roundedWeights hx)

theorem tendsto_pentagonMass_roundedWeights (g : Graph V) {x : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) :
    Tendsto (fun n => pentagonMass g (roundedWeights x n)) atTop
      (𝓝 (pentagonMass g x)) :=
  tendsto_pentagonMass g (tendsto_roundedWeights hx)

/-- A homogeneous squared inequality proved on all nonnegative integral vertex
weights extends to all nonnegative real vertex weights. -/
theorem squared_pentagon_bound_of_integral (g : Graph V) (c : ℝ)
    (hint : ∀ m : V → ℕ, pentagonMass g (fun v => (m v : ℝ)) ^ 2 ≤
      c * edgeMass g (fun v => (m v : ℝ)) ^ 5)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    pentagonMass g x ^ 2 ≤ c * edgeMass g x ^ 5 := by
  have hbound : ∀ n, pentagonMass g (roundedWeights x n) ^ 2 ≤
      c * edgeMass g (roundedWeights x n) ^ 5 := by
    intro n
    let m : V → ℕ := fun v => ⌊x v * (n : ℝ)⌋₊
    have h := mul_le_mul_of_nonneg_left (hint m) (by positivity : 0 ≤ ((n : ℝ)⁻¹) ^ 10)
    change pentagonMass g (fun v => (n : ℝ)⁻¹ * (m v : ℝ)) ^ 2 ≤
      c * edgeMass g (fun v => (n : ℝ)⁻¹ * (m v : ℝ)) ^ 5
    rw [pentagonMass_scale, edgeMass_scale]
    convert h using 1 <;> ring
  exact le_of_tendsto_of_tendsto
    ((tendsto_pentagonMass_roundedWeights g hx).pow 2)
    (((tendsto_edgeMass_roundedWeights g hx).pow 5).const_mul c)
    (Eventually.of_forall hbound)

theorem squared_pentagon_bound_integral_iff (g : Graph V) (c : ℝ) :
    (∀ m : V → ℕ, pentagonMass g (fun v => (m v : ℝ)) ^ 2 ≤
      c * edgeMass g (fun v => (m v : ℝ)) ^ 5) ↔
    (∀ x : V → ℝ, (∀ v, 0 ≤ x v) →
      pentagonMass g x ^ 2 ≤ c * edgeMass g x ^ 5) := by
  constructor
  · intro h x hx
    exact squared_pentagon_bound_of_integral g c h hx
  · intro h m
    exact h (fun v => (m v : ℝ)) (fun v => Nat.cast_nonneg (m v))

end InducedPentagons.Paper

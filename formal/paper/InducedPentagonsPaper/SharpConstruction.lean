import InducedPentagonsPaper.PentagonCount
import Mathlib.Analysis.Real.Sqrt

/-! The exact sharp-constant equality for the balanced Clebsch construction. -/

noncomputable section

namespace InducedPentagons.Paper

def sharpConstant : ℝ := 3 / (50 * Real.sqrt 10)

theorem sharpConstant_positive : 0 < sharpConstant := by
  unfold sharpConstant
  positivity

theorem sharpConstant_sq : sharpConstant ^ 2 = (9 / 25000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hp : Real.sqrt (10 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold sharpConstant
  field_simp
  nlinarith

theorem clebsch_balanced_squared_equality (k : ℝ) :
    pentagonMass clebsch (fun _ => k) ^ 2 =
      (9 / 25000 : ℝ) * edgeMass clebsch (fun _ => k) ^ 5 := by
  rw [clebsch_balanced_pentagonMass, clebsch_balanced_edgeMass]
  ring

/-- Here E² sqrt(E) is the nonnegative-real form of E^(5/2), including E=0. -/
theorem clebsch_balanced_sharp_equality {k : ℝ} (hk : 0 ≤ k) :
    pentagonMass clebsch (fun _ => k) = sharpConstant *
      edgeMass clebsch (fun _ => k) ^ 2 * Real.sqrt (edgeMass clebsch (fun _ => k)) := by
  have hE : 0 ≤ edgeMass clebsch (fun _ => k) := edgeMass_nonnegative clebsch (fun _ => hk)
  have hC : 0 ≤ pentagonMass clebsch (fun _ => k) := pentagonMass_nonnegative clebsch (fun _ => hk)
  have hR : 0 ≤ sharpConstant * edgeMass clebsch (fun _ => k) ^ 2 *
      Real.sqrt (edgeMass clebsch (fun _ => k)) :=
    mul_nonneg (mul_nonneg sharpConstant_positive.le (sq_nonneg _)) (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ hC hR).mp
  rw [clebsch_balanced_squared_equality, mul_pow, mul_pow,
    sharpConstant_sq, Real.sq_sqrt hE]
  ring

theorem clebsch_squaredRatio_unit : squaredRatio clebsch (fun _ => 1) = (9 / 25000 : ℝ) := by
  unfold squaredRatio
  rw [clebsch_pentagonMass_unit, clebsch_edgeMass_unit]
  norm_num

theorem clebsch_balanced_squaredRatio {k : ℝ} (hk : k ≠ 0) :
    squaredRatio clebsch (fun _ => k) = (9 / 25000 : ℝ) := by
  have h := squaredRatio_scale clebsch (fun _ => 1) hk
  simpa only [mul_one, clebsch_squaredRatio_unit] using h

end InducedPentagons.Paper

import InducedPentagonsPaper.ScalarProfile
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace InducedPentagons.Paper

/-- The manuscript's edge-scale penalty in the sharp phase law. -/
def edgePhasePenalty (u : ℝ) : ℝ := max (12 * u) (-4 * u)

/-- The coefficient of `m²` in the phase law. -/
def phaseCoefficient (a : ℝ) : ℝ := (1 - a) * min (3 * a) 1 / 80

theorem edgePhasePenalty_nonnegative (u : ℝ) : 0 ≤ edgePhasePenalty u := by
  unfold edgePhasePenalty
  by_cases hu : 0 ≤ u
  · exact (mul_nonneg (by norm_num) hu).trans (le_max_left _ _)
  · exact (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (le_of_not_ge hu)).trans
      (le_max_right _ _)

theorem edgePhasePenalty_scale (u : ℝ) :
    edgePhasePenalty (5 * u) = phasePenalty u := by
  unfold edgePhasePenalty phasePenalty
  congr 1 <;> ring

theorem edgePhasePenalty_add (u v : ℝ) :
    edgePhasePenalty (u + v) ≤ edgePhasePenalty u + edgePhasePenalty v := by
  have hu₁ : 12 * u ≤ edgePhasePenalty u := le_max_left _ _
  have hu₂ : -4 * u ≤ edgePhasePenalty u := le_max_right _ _
  have hv₁ : 12 * v ≤ edgePhasePenalty v := le_max_left _ _
  have hv₂ : -4 * v ≤ edgePhasePenalty v := le_max_right _ _
  apply max_le <;> linarith

/-- The explicit Lipschitz estimate used to absorb edge and phase errors. -/
theorem edgePhasePenalty_le_add_abs (u v : ℝ) :
    edgePhasePenalty u ≤ edgePhasePenalty v + 12 * |u - v| := by
  have hv₁ : 12 * v ≤ edgePhasePenalty v := le_max_left _ _
  have hv₂ : -4 * v ≤ edgePhasePenalty v := le_max_right _ _
  have h₁ := le_abs_self (u - v)
  have h₂ := neg_le_abs (u - v)
  have h₃ := abs_nonneg (u - v)
  apply max_le <;> linarith

theorem edgePhasePenalty_lipschitz (u v : ℝ) :
    |edgePhasePenalty u - edgePhasePenalty v| ≤ 12 * |u - v| := by
  apply abs_le.mpr
  constructor
  · have h := edgePhasePenalty_le_add_abs v u
    rw [abs_sub_comm v u] at h
    linarith
  · have h := edgePhasePenalty_le_add_abs u v
    linarith

/-- The spectral interval in equation (62) controls the template penalty. -/
theorem edgePhasePenalty_le_variance {a v : ℝ}
    (hlo : -3 * v / 2 ≤ a) (hhi : a ≤ v / 2) :
    edgePhasePenalty a ≤ 6 * v := by
  apply max_le <;> linarith

/-- Adding and deleting edges contributes enough to pay the adjustment penalty. -/
theorem edgePhasePenalty_le_edit_cost {plus minus k : ℝ}
    (hp : 0 ≤ plus) (hm : 0 ≤ minus) (hk : 0 < k) :
    edgePhasePenalty ((plus - minus) / k) ≤ 12 * (plus + minus) / k := by
  have hkp : 0 ≤ plus / k := div_nonneg hp hk.le
  have hkm : 0 ≤ minus / k := div_nonneg hm hk.le
  unfold edgePhasePenalty
  rw [sub_div, mul_add, add_div, mul_div_assoc, mul_div_assoc]
  apply max_le <;> nlinarith

/-- The paper's `m²` normalization of the scalar optimum. -/
theorem phaseCoefficient_eq_phaseCost (a : ℝ) :
    phaseCoefficient a = phaseCost a / 1600 := by
  unfold phaseCoefficient phaseCost
  ring

theorem phaseCoefficient_nonnegative {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ phaseCoefficient a := by
  unfold phaseCoefficient
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha1)
    (le_min (by linarith) (by norm_num))) (by norm_num)

theorem phaseCoefficient_le (a : ℝ) :
    phaseCoefficient a ≤ 1 / 120 := by
  unfold phaseCoefficient
  by_cases h : a ≤ 1 / 3
  · rw [min_eq_left (by linarith : 3 * a ≤ 1)]
    have hp := mul_nonneg (show 0 ≤ 1 / 3 - a by linarith)
      (show 0 ≤ 2 / 3 - a by linarith)
    nlinarith
  · rw [min_eq_right (by linarith : 1 ≤ 3 * a)]
    nlinarith

theorem phaseCoefficient_maximum : phaseCoefficient (1 / 3) = 1 / 120 := by
  norm_num [phaseCoefficient]

theorem phaseCoefficient_endpoints :
    phaseCoefficient 0 = 0 ∧ phaseCoefficient 1 = 0 := by
  norm_num [phaseCoefficient]

/-- Exact factorization behind the phase replacement after equation (67). -/
theorem phase_edge_residual (k N : ℝ) (hk : k ≠ 0) :
    (40 * k ^ 2 - 5 * N ^ 2 / 32) / k =
      5 * (16 * k - N) - 5 / (32 * k) * (16 * k - N) ^ 2 := by
  field_simp
  ring

/-- The phase and integer offset recover the real class-size discrepancy. -/
theorem phase_integer_offset (k : ℝ) (N : ℤ) :
    Int.fract (16 * k) + ((⌊16 * k⌋ - N : ℤ) : ℝ) = 16 * k - N := by
  push_cast
  linarith [Int.fract_add_floor (16 * k)]

/-- The phase replacement error is exactly the nonnegative quadratic remainder. -/
theorem phase_edge_residual_error {k : ℝ} (hk : 0 < k) (N : ℤ) :
    |(40 * k ^ 2 - 5 * (N : ℝ) ^ 2 / 32) / k -
      5 * (Int.fract (16 * k) + ((⌊16 * k⌋ - N : ℤ) : ℝ))| =
      5 / (32 * k) * (16 * k - N) ^ 2 := by
  rw [phase_integer_offset, phase_edge_residual k N hk.ne']
  have hn : 0 ≤ 5 / (32 * k) * (16 * k - N) ^ 2 :=
    mul_nonneg (div_nonneg (by norm_num) (by positivity)) (sq_nonneg _)
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hn]

/-- Quantitative scalar reduction of equations (62), (63), and (67).
All three error bounds are explicit; no asymptotic or graph-counting assumption
is silently discharged here. -/
theorem phase_deficit_reduction (profiles : List (ℝ × ℝ))
    (henv : ∀ p ∈ profiles,
      0 ≤ p.1 ∧ p.2 ≤ (12 / 5 : ℝ) * p.1 ^ 2 ∧ p.2 ≤ 60)
    {a s v plus minus k r deficit edgeError phaseError deficitError : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (ell : ℤ)
    (hp : 0 ≤ plus) (hm : 0 ≤ minus) (hk : 0 < k)
    (hslo : -3 * v / 2 ≤ s) (hshi : s ≤ v / 2)
    (hedge : |r - (s + (profiles.map Prod.fst).sum + (plus - minus) / k)| ≤ edgeError)
    (hphase : |r - 5 * (a + ell)| ≤ phaseError)
    (hdeficit : 6 * v + (profiles.map (fun p => 12 * p.1 - p.2)).sum +
      12 * (plus + minus) / k ≤ deficit + deficitError) :
    phaseCost a ≤ deficit + deficitError + 12 * (edgeError + phaseError) := by
  have hscalar := scalar_profile profiles henv ha ha1 ell
  have hsum : (profiles.map (fun p => p.1 / 5)).sum =
      (profiles.map Prod.fst).sum / 5 := by
    simp only [div_eq_mul_inv, List.sum_map_mul_right]
  have hscale : phasePenalty (a + ell - (profiles.map (fun p => p.1 / 5)).sum) =
      edgePhasePenalty (5 * (a + ell) - (profiles.map Prod.fst).sum) := by
    rw [hsum]
    unfold phasePenalty edgePhasePenalty
    congr 1 <;> ring
  rw [hscale] at hscalar
  have hs := edgePhasePenalty_le_variance hslo hshi
  have he := edgePhasePenalty_le_edit_cost hp hm hk
  have hadd := edgePhasePenalty_add s ((plus - minus) / k)
  have h₁ := edgePhasePenalty_le_add_abs
    (r - (profiles.map Prod.fst).sum) (s + (plus - minus) / k)
  have h₁abs : r - (profiles.map Prod.fst).sum - (s + (plus - minus) / k) =
      r - (s + (profiles.map Prod.fst).sum + (plus - minus) / k) := by ring
  rw [h₁abs] at h₁
  have h₂ := edgePhasePenalty_le_add_abs
    (5 * (a + ell) - (profiles.map Prod.fst).sum) (r - (profiles.map Prod.fst).sum)
  have h₂abs : 5 * (a + ell) - (profiles.map Prod.fst).sum -
      (r - (profiles.map Prod.fst).sum) = -(r - 5 * (a + ell)) := by ring
  rw [h₂abs, abs_neg] at h₂
  linarith

/-- Both competing constructions attain the scalar lower bound in their phase region. -/
theorem reduced_scalar_profile_sharp {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      phaseCost a = 60 * t * (1 - t) + phasePenalty (a - t) := by
  by_cases h : 3 * a ≤ 1
  · refine ⟨a, ha, ha1, ?_⟩
    simp only [phaseCost, min_eq_left h, sub_self, phasePenalty]
    ring_nf
    norm_num
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    have hp : 60 * (a - 1) ≤ -20 * (a - 1) := by linarith
    simp only [phaseCost, min_eq_right (le_of_not_ge h), phasePenalty, max_eq_right hp]
    ring

/-- The phase coefficient is continuous, including at its switching point. -/
theorem phaseCoefficient_continuous : Continuous phaseCoefficient := by
  unfold phaseCoefficient
  fun_prop

/-- Exact range of the proposed second-order coefficient on one full phase period. -/
theorem phaseCoefficient_range :
    phaseCoefficient '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / 120) := by
  apply Set.Subset.antisymm
  · rintro y ⟨a, ha, rfl⟩
    exact ⟨phaseCoefficient_nonnegative ha.1 ha.2, phaseCoefficient_le a⟩
  · intro y hy
    have hz : phaseCoefficient 0 = 0 := phaseCoefficient_endpoints.1
    have hiv := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      phaseCoefficient_continuous.continuousOn
    rw [hz, phaseCoefficient_maximum] at hiv
    rcases hiv hy with ⟨a, ha, hay⟩
    exact ⟨a, ⟨ha.1, ha.2.trans (by norm_num)⟩, hay⟩

end InducedPentagons.Paper

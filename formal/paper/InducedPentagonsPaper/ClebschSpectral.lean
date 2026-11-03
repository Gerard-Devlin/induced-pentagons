import InducedPentagonsPaper.OrderedEdgeSum
import InducedPentagonsPaper.PhaseArithmetic

open scoped BigOperators

noncomputable section
namespace InducedPentagons.Paper

/-- Weighted adjacency action of the actual Clebsch graph. -/
def clebschAdjacencyAction (x : Fin 16 → ℝ) (i : Fin 16) : ℝ :=
  ∑ j, if clebsch.adj i j = true then x j else 0

def classVariance (x : Fin 16 → ℝ) : ℝ := ∑ i, x i ^ 2

def clebschQuadratic (x : Fin 16 → ℝ) : ℝ := ∑ i, x i * clebschAdjacencyAction x i

set_option maxHeartbeats 0 in
/-- Sum-of-squares certificate for the Clebsch upper spectral bound. -/
theorem clebsch_spectral_upper_identity (x : Fin 16 → ℝ) :
    (∑ i, (clebschAdjacencyAction x i - x i) ^ 2) =
      4 * classVariance x - 4 * clebschQuadratic x + 2 * (∑ i, x i) ^ 2 := by
  simp [clebschAdjacencyAction, classVariance, clebschQuadratic,
    Fin.sum_univ_succ, clebsch, clebschAdj]
  ring

set_option maxHeartbeats 0 in
/-- Sum-of-squares certificate for the Clebsch lower spectral bound. -/
theorem clebsch_spectral_lower_identity (x : Fin 16 → ℝ) :
    (∑ i, (clebschAdjacencyAction x i + 3 * x i) ^ 2) =
      12 * classVariance x + 4 * clebschQuadratic x + 2 * (∑ i, x i) ^ 2 := by
  simp [clebschAdjacencyAction, classVariance, clebschQuadratic,
    Fin.sum_univ_succ, clebsch, clebschAdj]
  ring

/-- Equation (62) before division by the positive scale `2k`. -/
theorem clebsch_spectral_interval {x : Fin 16 → ℝ} (hx : ∑ i, x i = 0) :
    -3 * classVariance x ≤ clebschQuadratic x ∧
      clebschQuadratic x ≤ classVariance x := by
  have hlo := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg (clebschAdjacencyAction x i + 3 * x i))
  have hhi := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg (clebschAdjacencyAction x i - x i))
  rw [clebsch_spectral_lower_identity, hx] at hlo
  rw [clebsch_spectral_upper_identity, hx] at hhi
  constructor <;> nlinarith

/-- The graph-defined quadratic form is twice the existing weighted edge mass. -/
theorem clebschQuadratic_eq_twice_edgeMass (x : Fin 16 → ℝ) :
    clebschQuadratic x = 2 * edgeMass clebsch x := by
  unfold clebschQuadratic clebschAdjacencyAction edgeMass
  rw [dart_sum_eq_doubleSum]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  ring

/-- The variance penalty required by the phase law follows from actual Clebsch adjacency. -/
theorem clebsch_phase_variance_penalty {x : Fin 16 → ℝ} (hx : ∑ i, x i = 0)
    {k : ℝ} (hk : 0 < k) :
    edgePhasePenalty (clebschQuadratic x / (2 * k)) ≤ 6 * (classVariance x / k) := by
  rcases clebsch_spectral_interval hx with ⟨hlo, hhi⟩
  apply edgePhasePenalty_le_variance
  · apply (le_div_iff₀ (by positivity : 0 < 2 * k)).mpr
    have heq : -3 * (classVariance x / k) / 2 * (2 * k) = -3 * classVariance x := by
      field_simp
    rw [heq]
    exact hlo
  · apply (div_le_iff₀ (by positivity : 0 < 2 * k)).mpr
    have heq : classVariance x / k / 2 * (2 * k) = classVariance x := by
      field_simp
    rw [heq]
    exact hhi

/-- Centering the sixteen class sizes gives the zero-sum vector used in (61). -/
theorem centered_class_sum (n : Fin 16 → ℝ) :
    (∑ i, (n i - (∑ j, n j) / 16)) = 0 := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

set_option maxHeartbeats 0 in
/-- Translation by a constant in the actual weighted Clebsch edge polynomial. -/
theorem clebsch_edgeMass_translate (x : Fin 16 → ℝ) (q : ℝ) :
    edgeMass clebsch (fun i => x i + q) =
      edgeMass clebsch x + 5 * q * (∑ i, x i) + 40 * q ^ 2 := by
  simp [edgeMass_eq_orderedEdgeSum, orderedEdgeSum,
    Fin.sum_univ_succ, clebsch, clebschAdj]
  ring

/-- The exact edge expansion used immediately before equation (63). -/
theorem clebsch_edgeMass_centered (n : Fin 16 → ℝ) :
    edgeMass clebsch n = 5 * (∑ i, n i) ^ 2 / 32 +
      clebschQuadratic (fun i => n i - (∑ j, n j) / 16) / 2 := by
  have ht := clebsch_edgeMass_translate
    (fun i => n i - (∑ j, n j) / 16) ((∑ j, n j) / 16)
  simp only [sub_add_cancel, centered_class_sum, mul_zero, add_zero] at ht
  rw [clebschQuadratic_eq_twice_edgeMass]
  rw [ht]
  ring

/-- Equation (62) for actual centered class sizes and any positive scale. -/
theorem clebsch_centered_spectral_interval (n : Fin 16 → ℝ) {k : ℝ} (hk : 0 < k) :
    let h := fun i => n i - (∑ j, n j) / 16;
    let a := clebschQuadratic h / (2 * k);
    let v := classVariance h / k;
    -3 * v / 2 ≤ a ∧ a ≤ v / 2 := by
  dsimp
  rcases clebsch_spectral_interval (centered_class_sum n) with ⟨hlo, hhi⟩
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * k)).mpr
    convert hlo using 1; field_simp; simp [mul_comm]
  · apply (div_le_iff₀ (by positivity : 0 < 2 * k)).mpr
    convert hhi using 1; field_simp; simp [mul_comm]

end InducedPentagons.Paper

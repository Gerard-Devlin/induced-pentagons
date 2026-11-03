import InducedPentagonsPaper.ClebschSpectral
import InducedPentagonsPaper.PentagonSubsetCount
import InducedPentagons.Construction

open scoped BigOperators

noncomputable section
namespace InducedPentagons.Paper

/-- Homogeneous pieces of a five-vertex product translated by a constant. -/
def pentagonLinear (p : PentagonTuple 16) (x : Fin 16 → ℝ) : ℝ :=
  x p.a + x p.b + x p.c + x p.d + x p.e

def pentagonQuadratic (p : PentagonTuple 16) (x : Fin 16 → ℝ) : ℝ :=
  x p.a * x p.b + x p.a * x p.c + x p.a * x p.d + x p.a * x p.e +
  x p.b * x p.c + x p.b * x p.d + x p.b * x p.e +
  x p.c * x p.d + x p.c * x p.e + x p.d * x p.e

def pentagonCubic (p : PentagonTuple 16) (x : Fin 16 → ℝ) : ℝ :=
  x p.a * x p.b * x p.c + x p.a * x p.b * x p.d + x p.a * x p.b * x p.e +
  x p.a * x p.c * x p.d + x p.a * x p.c * x p.e + x p.a * x p.d * x p.e +
  x p.b * x p.c * x p.d + x p.b * x p.c * x p.e + x p.b * x p.d * x p.e +
  x p.c * x p.d * x p.e

def pentagonQuartic (p : PentagonTuple 16) (x : Fin 16 → ℝ) : ℝ :=
  x p.a * x p.b * x p.c * x p.d + x p.a * x p.b * x p.c * x p.e +
  x p.a * x p.b * x p.d * x p.e + x p.a * x p.c * x p.d * x p.e +
  x p.b * x p.c * x p.d * x p.e

def pentagonQuintic (p : PentagonTuple 16) (x : Fin 16 → ℝ) : ℝ :=
  x p.a * x p.b * x p.c * x p.d * x p.e

theorem pentagon_product_translate (p : PentagonTuple 16) (x : Fin 16 → ℝ) (q : ℝ) :
    (∏ i, (x (p.vertex i) + q)) = q ^ 5 + q ^ 4 * pentagonLinear p x +
      q ^ 3 * pentagonQuadratic p x + q ^ 2 * pentagonCubic p x +
      q * pentagonQuartic p x + pentagonQuintic p x := by
  simp [Fin.prod_univ_succ, PentagonTuple.vertex, pentagonLinear, pentagonQuadratic,
    pentagonCubic, pentagonQuartic, pentagonQuintic]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Every Clebsch vertex belongs to sixty normalized induced pentagons. -/
theorem clebsch_pentagon_linear_sum (x : Fin 16 → ℝ) :
    ((inducedPentagons clebsch).map (fun p => pentagonLinear p x)).sum =
      60 * (∑ i, x i) := by
  rw [clebsch_pentagon_enumeration]
  simp [Generated.clebschPentagonData, pentagonLinear, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The exact quadratic part: adjacent pairs occur 24 times and nonadjacent
pairs 12 times in the complete normalized pentagon enumeration. -/
theorem clebsch_pentagon_quadratic_sum (x : Fin 16 → ℝ) :
    ((inducedPentagons clebsch).map (fun p => pentagonQuadratic p x)).sum =
      6 * (∑ i, x i) ^ 2 - 6 * classVariance x + 6 * clebschQuadratic x := by
  rw [clebsch_pentagon_enumeration]
  simp [Generated.clebschPentagonData, pentagonQuadratic, classVariance,
    clebschQuadratic, clebschAdjacencyAction, Fin.sum_univ_succ, clebsch, clebschAdj]
  ring

def clebschPentagonRemainder (x : Fin 16 → ℝ) (q : ℝ) : ℝ :=
  q ^ 2 * ((inducedPentagons clebsch).map (fun p => pentagonCubic p x)).sum +
  q * ((inducedPentagons clebsch).map (fun p => pentagonQuartic p x)).sum +
  ((inducedPentagons clebsch).map (fun p => pentagonQuintic p x)).sum

/-- Exact second-order expansion of the graph-defined weighted pentagon count. -/
theorem clebsch_pentagonMass_translate (x : Fin 16 → ℝ) (q : ℝ) :
    pentagonMass clebsch (fun i => x i + q) =
      192 * q ^ 5 + 60 * q ^ 4 * (∑ i, x i) +
      6 * q ^ 3 * ((∑ i, x i) ^ 2 - classVariance x + clebschQuadratic x) +
      clebschPentagonRemainder x q := by
  rw [pentagonMass_eq_normalizedMass]
  unfold normalizedPentagonMass
  simp_rw [pentagon_product_translate]
  simp only [List.sum_map_add, List.sum_map_mul_left]
  rw [clebsch_pentagon_linear_sum, clebsch_pentagon_quadratic_sum]
  simp only [List.map_const', List.sum_replicate, clebsch_pentagons, nsmul_eq_mul,
    Nat.cast_ofNat]
  unfold clebschPentagonRemainder
  ring

/-- At zero total displacement the linear term vanishes. -/
theorem clebsch_pentagonMass_centered {x : Fin 16 → ℝ} (hx : ∑ i, x i = 0) (q : ℝ) :
    pentagonMass clebsch (fun i => x i + q) =
      192 * q ^ 5 + 6 * q ^ 3 * (clebschQuadratic x - classVariance x) +
      clebschPentagonRemainder x q := by
  rw [clebsch_pentagonMass_translate, hx]
  ring

end InducedPentagons.Paper

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

private theorem abs_list_sum_le {s : List ℝ} {c : ℝ}
    (h : ∀ a ∈ s, |a| ≤ c) : |s.sum| ≤ s.length * c := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha := h a (by simp)
    have hs := ih (by intro b hb; exact h b (by simp [hb]))
    have ht := abs_add_le a s.sum
    linarith

private theorem abs_triple_le {a b c r : ℝ} (hr : 0 ≤ r)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hc : |c| ≤ r) : |a * b * c| ≤ r ^ 3 := by
  calc
    |a * b * c| = |a| * |b| * |c| := by simp [abs_mul]
    _ ≤ r * r * r := mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hr)
      hc (abs_nonneg _) (mul_nonneg hr hr)
    _ = r ^ 3 := by ring

private theorem abs_quadruple_le {a b c d r : ℝ} (hr : 0 ≤ r)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hc : |c| ≤ r) (hd : |d| ≤ r) :
    |a * b * c * d| ≤ r ^ 4 := by
  calc
    |a * b * c * d| = |a * b * c| * |d| := abs_mul _ _
    _ ≤ r ^ 3 * r := mul_le_mul (abs_triple_le hr ha hb hc) hd
      (abs_nonneg _) (by positivity)
    _ = r ^ 4 := by ring

private theorem abs_quintuple_le {a b c d e r : ℝ} (hr : 0 ≤ r)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hc : |c| ≤ r) (hd : |d| ≤ r)
    (he : |e| ≤ r) : |a * b * c * d * e| ≤ r ^ 5 := by
  calc
    |a * b * c * d * e| = |a * b * c * d| * |e| := abs_mul _ _
    _ ≤ r ^ 4 * r := mul_le_mul (abs_quadruple_le hr ha hb hc hd) he
      (abs_nonneg _) (by positivity)
    _ = r ^ 5 := by ring

/-- Uniform cubic coefficient bound from coordinate bounds. -/
theorem pentagonCubic_abs_le (p : PentagonTuple 16) {x : Fin 16 → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hx : ∀ i, |x i| ≤ r) : |pentagonCubic p x| ≤ 10 * r ^ 3 := by
  have h := abs_list_sum_le (s := [
    x p.a * x p.b * x p.c, x p.a * x p.b * x p.d, x p.a * x p.b * x p.e,
    x p.a * x p.c * x p.d, x p.a * x p.c * x p.e, x p.a * x p.d * x p.e,
    x p.b * x p.c * x p.d, x p.b * x p.c * x p.e, x p.b * x p.d * x p.e,
    x p.c * x p.d * x p.e]) (c := r ^ 3) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact abs_triple_le hr (hx _) (hx _) (hx _))
  simpa [pentagonCubic, add_assoc] using h

/-- Uniform quartic coefficient bound from coordinate bounds. -/
theorem pentagonQuartic_abs_le (p : PentagonTuple 16) {x : Fin 16 → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hx : ∀ i, |x i| ≤ r) : |pentagonQuartic p x| ≤ 5 * r ^ 4 := by
  have h := abs_list_sum_le (s := [
    x p.a * x p.b * x p.c * x p.d, x p.a * x p.b * x p.c * x p.e,
    x p.a * x p.b * x p.d * x p.e, x p.a * x p.c * x p.d * x p.e,
    x p.b * x p.c * x p.d * x p.e]) (c := r ^ 4) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        exact abs_quadruple_le hr (hx _) (hx _) (hx _) (hx _))
  simpa [pentagonQuartic, add_assoc] using h

/-- Uniform quintic coefficient bound from coordinate bounds. -/
theorem pentagonQuintic_abs_le (p : PentagonTuple 16) {x : Fin 16 → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hx : ∀ i, |x i| ≤ r) : |pentagonQuintic p x| ≤ r ^ 5 := by
  exact abs_quintuple_le hr (hx _) (hx _) (hx _) (hx _) (hx _)

/-- Explicit bound on every term omitted from the quadratic expansion. -/
theorem clebschPentagonRemainder_abs_le {x : Fin 16 → ℝ} {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hx : ∀ i, |x i| ≤ r) :
    |clebschPentagonRemainder x q| ≤ 1920 * q ^ 2 * r ^ 3 +
      960 * q * r ^ 4 + 192 * r ^ 5 := by
  have hc : |((inducedPentagons clebsch).map (fun p => pentagonCubic p x)).sum| ≤
      192 * (10 * r ^ 3) := by
    convert abs_list_sum_le (s := (inducedPentagons clebsch).map
      (fun p => pentagonCubic p x)) (c := 10 * r ^ 3) (by
        intro a ha
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        exact pentagonCubic_abs_le p hr hx) using 1
    simp [List.length_map, clebsch_pentagons]
  have hd : |((inducedPentagons clebsch).map (fun p => pentagonQuartic p x)).sum| ≤
      192 * (5 * r ^ 4) := by
    convert abs_list_sum_le (s := (inducedPentagons clebsch).map
      (fun p => pentagonQuartic p x)) (c := 5 * r ^ 4) (by
        intro a ha
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        exact pentagonQuartic_abs_le p hr hx) using 1
    simp [List.length_map, clebsch_pentagons]
  have he : |((inducedPentagons clebsch).map (fun p => pentagonQuintic p x)).sum| ≤
      192 * r ^ 5 := by
    convert abs_list_sum_le (s := (inducedPentagons clebsch).map
      (fun p => pentagonQuintic p x)) (c := r ^ 5) (by
        intro a ha
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        exact pentagonQuintic_abs_le p hr hx) using 1
    simp [List.length_map, clebsch_pentagons]
  unfold clebschPentagonRemainder
  calc
    _ ≤ |q ^ 2 * ((inducedPentagons clebsch).map (fun p => pentagonCubic p x)).sum| +
        |q * ((inducedPentagons clebsch).map (fun p => pentagonQuartic p x)).sum| +
        |((inducedPentagons clebsch).map (fun p => pentagonQuintic p x)).sum| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ q ^ 2 * (192 * (10 * r ^ 3)) + q * (192 * (5 * r ^ 4)) + 192 * r ^ 5 := by
      simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg (sq_nonneg q)]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc (sq_nonneg q))
        (mul_le_mul_of_nonneg_left hd hq)) he
    _ = _ := by ring

/-- A cubic error estimate whenever the coordinate radius is at most the scale. -/
theorem clebschPentagonRemainder_cubic_bound {x : Fin 16 → ℝ} {q r : ℝ}
    (hr : 0 ≤ r) (hrq : r ≤ q) (hx : ∀ i, |x i| ≤ r) :
    |clebschPentagonRemainder x q| ≤ 3072 * q ^ 2 * r ^ 3 := by
  have hq : 0 ≤ q := hr.trans hrq
  have h4 : q * r ^ 4 ≤ q ^ 2 * r ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrq) (mul_nonneg hq (pow_nonneg hr 3))]
  have h5 : r ^ 5 ≤ q ^ 2 * r ^ 3 := by
    have hs : r ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hr hrq 2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (pow_nonneg hr 3)]
  have he := clebschPentagonRemainder_abs_le hq hr hx
  nlinarith

/-- The Euclidean radius controls every class displacement. -/
theorem clebsch_coordinate_le_sqrt_variance (x : Fin 16 → ℝ) (i : Fin 16) :
    |x i| ≤ Real.sqrt (classVariance x) := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- Quantitative quadratic expansion at every zero-sum displacement of small radius. -/
theorem clebsch_pentagonMass_quadratic_error {x : Fin 16 → ℝ} {q : ℝ}
    (hx : ∑ i, x i = 0) (hsmall : Real.sqrt (classVariance x) ≤ q) :
    |pentagonMass clebsch (fun i => x i + q) -
      (192 * q ^ 5 + 6 * q ^ 3 * (clebschQuadratic x - classVariance x))| ≤
        3072 * q ^ 2 * Real.sqrt (classVariance x) ^ 3 := by
  rw [clebsch_pentagonMass_centered hx, add_sub_cancel_left]
  exact clebschPentagonRemainder_cubic_bound (Real.sqrt_nonneg _) hsmall
    (clebsch_coordinate_le_sqrt_variance x)

end InducedPentagons.Paper

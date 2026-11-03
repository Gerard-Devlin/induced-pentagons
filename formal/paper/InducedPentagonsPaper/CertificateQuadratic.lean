import Mathlib.Tactic
import InducedPentagons.Generated.Metadata

/-! The actual certificate Gram entries are weighted outer products. Their
quadratic forms, and every nonnegative average of them, are nonnegative.
Applications to joint densities must supply the conditional-product identity. -/

open scoped BigOperators

namespace InducedPentagons.Paper

private theorem source_foldl_sum (ss : List SquareSource) (b i j : Nat) (z : Int) :
    ss.foldl (fun a s => if s.block == b then
      a + s.coefficient.scaled * s.vector[i]! * s.vector[j]! else a) z =
    z + (ss.map (fun s => if s.block = b then
      s.coefficient.scaled * s.vector[i]! * s.vector[j]! else 0)).sum := by
  simp only [beq_iff_eq]
  induction ss generalizing z with
  | nil => simp
  | cons s ss ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases h : s.block = b <;> simp [h, ih, add_assoc]

theorem gramEntry_eq_square_sum (c : Certificate) (b i j : Nat) :
    gramEntry c b i j = (c.squares.toList.map (fun s => if s.block = b then
      s.coefficient.scaled * s.vector[i]! * s.vector[j]! else 0)).sum := by
  simpa only [gramEntry, zero_add] using source_foldl_sum c.squares.toList b i j 0

def sourceQuadratic {d : Nat} (s : SquareSource) (x : Fin d → ℚ) : ℚ :=
  (s.coefficient.scaled : ℚ) * (∑ i, ((s.vector[i.val]! : Int) : ℚ) * x i) ^ 2

def certificateQuadratic (c : Certificate) (b d : Nat) (x : Fin d → ℚ) : ℚ :=
  ∑ i, ∑ j, (gramEntry c b i.val j.val : ℚ) * x i * x j

private theorem rankOne_quadratic {d : Nat} (w : ℚ) (v x : Fin d → ℚ) :
    (∑ i, ∑ j, w * v i * v j * x i * x j) =
      w * (∑ i, v i * x i) ^ 2 := by
  calc
    _ = ∑ i, ∑ j, w * (v i * x i) * (v j * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = w * (∑ i, v i * x i) * (∑ j, v j * x j) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by ring

private theorem square_sum_quadratic (ss : List SquareSource) (b d : Nat)
    (x : Fin d → ℚ) :
    (∑ i, ∑ j, (((ss.map (fun s => if s.block = b then
      s.coefficient.scaled * s.vector[i.val]! * s.vector[j.val]! else 0)).sum : Int) : ℚ)
      * x i * x j) =
    (ss.map (fun s => if s.block = b then sourceQuadratic s x else 0)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, add_mul, Finset.sum_add_distrib, ih]
    by_cases h : s.block = b
    · simp only [h, ite_true, Int.cast_mul, sourceQuadratic]
      rw [rankOne_quadratic]
    · simp [h]

theorem certificateQuadratic_eq_squares (c : Certificate) (b d : Nat)
    (x : Fin d → ℚ) :
    certificateQuadratic c b d x =
      (c.squares.toList.map (fun s => if s.block = b then sourceQuadratic s x else 0)).sum := by
  unfold certificateQuadratic
  simp_rw [gramEntry_eq_square_sum]
  exact square_sum_quadratic c.squares.toList b d x

theorem checkSquare_scaled_positive {c : Certificate} {s : SquareSource}
    (h : checkSquare c s = true) : 0 < s.coefficient.scaled := by
  simp only [checkSquare, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem metadata_square_checks {c : Certificate} (h : checkMetadata c = true) :
    ∀ s ∈ c.squares.toList, checkSquare c s = true := by
  simp only [checkMetadata, Bool.and_eq_true_iff] at h
  have hall : c.squares.toList.all (checkSquare c) = true := by tauto
  exact List.all_eq_true.mp hall


theorem sourceQuadratic_nonnegative {d : Nat} (s : SquareSource)
    (hs : 0 ≤ s.coefficient.scaled) (x : Fin d → ℚ) : 0 ≤ sourceQuadratic s x := by
  exact mul_nonneg (by exact_mod_cast hs) (sq_nonneg _)

theorem certificateQuadratic_nonnegative (c : Certificate) (hc : checkMetadata c = true)
    (b d : Nat) (x : Fin d → ℚ) : 0 ≤ certificateQuadratic c b d x := by
  rw [certificateQuadratic_eq_squares]
  apply List.sum_nonneg
  intro q hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  split
  · exact sourceQuadratic_nonnegative s
      (checkSquare_scaled_positive (metadata_square_checks hc s hs)).le x
  · exact le_rfl

theorem actual_certificateQuadratic_nonnegative (b d : Nat) (x : Fin d → ℚ) :
    0 ≤ certificateQuadratic Generated.certificate b d x :=
  certificateQuadratic_nonnegative _ Generated.metadata_checked b d x

def conditionalSquareAverage {Ω : Type} [Fintype Ω] (c : Certificate) (b d : Nat)
    (weight : Ω → ℚ) (density : Ω → Fin d → ℚ) : ℚ :=
  ∑ root, weight root * certificateQuadratic c b d (density root)

theorem conditionalSquareAverage_nonnegative {Ω : Type} [Fintype Ω]
    (c : Certificate) (hc : checkMetadata c = true) (b d : Nat)
    (weight : Ω → ℚ) (hw : ∀ root, 0 ≤ weight root) (density : Ω → Fin d → ℚ) :
    0 ≤ conditionalSquareAverage c b d weight density := by
  apply Finset.sum_nonneg
  intro root _
  exact mul_nonneg (hw root) (certificateQuadratic_nonnegative c hc b d _)

theorem actual_conditionalSquareAverage_nonnegative {Ω : Type} [Fintype Ω]
    (b d : Nat) (weight : Ω → ℚ) (hw : ∀ root, 0 ≤ weight root)
    (density : Ω → Fin d → ℚ) :
    0 ≤ conditionalSquareAverage Generated.certificate b d weight density :=
  conditionalSquareAverage_nonnegative _ Generated.metadata_checked b d weight hw density

def densityGramContraction (c : Certificate) (b d : Nat)
    (pairDensity : Fin d → Fin d → ℚ) : ℚ :=
  ∑ i, ∑ j, (gramEntry c b i.val j.val : ℚ) * pairDensity i j

theorem conditional_product_contraction {Ω : Type} [Fintype Ω]
    (c : Certificate) (b d : Nat) (weight : Ω → ℚ)
    (density : Ω → Fin d → ℚ) :
    densityGramContraction c b d
      (fun i j => ∑ root, weight root * density root i * density root j) =
    conditionalSquareAverage c b d weight density := by
  unfold densityGramContraction conditionalSquareAverage certificateQuadratic
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ i : Fin d, ∑ root : Ω, ∑ j : Fin d,
        (gramEntry c b i.val j.val : ℚ) *
          (weight root * density root i * density root j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ root : Ω, ∑ i : Fin d, ∑ j : Fin d,
        (gramEntry c b i.val j.val : ℚ) *
          (weight root * density root i * density root j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro root _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem actual_densityGramContraction_nonnegative {Ω : Type} [Fintype Ω]
    (b d : Nat) (weight : Ω → ℚ) (hw : ∀ root, 0 ≤ weight root)
    (density : Ω → Fin d → ℚ) (pairDensity : Fin d → Fin d → ℚ)
    (hproduct : ∀ i j, pairDensity i j =
      ∑ root, weight root * density root i * density root j) :
    0 ≤ densityGramContraction Generated.certificate b d pairDensity := by
  have he : pairDensity = fun i j =>
      ∑ root, weight root * density root i * density root j := by
    funext i j
    exact hproduct i j
  rw [he, conditional_product_contraction]
  exact actual_conditionalSquareAverage_nonnegative b d weight hw density


def normalizedCertificateQuadratic (c : Certificate) (b d : Nat)
    (density : Fin d → ℚ) : ℚ :=
  certificateQuadratic c b d density / (c.scale : ℚ)

theorem normalizedCertificateQuadratic_nonnegative (c : Certificate)
    (hc : checkMetadata c = true) (b d : Nat) (density : Fin d → ℚ) :
    0 ≤ normalizedCertificateQuadratic c b d density := by
  exact div_nonneg (certificateQuadratic_nonnegative c hc b d density) (Nat.cast_nonneg _)

theorem actual_normalizedCertificateQuadratic_nonnegative (b d : Nat)
    (density : Fin d → ℚ) :
    0 ≤ normalizedCertificateQuadratic Generated.certificate b d density :=
  normalizedCertificateQuadratic_nonnegative _ Generated.metadata_checked b d density

theorem actual_normalizedDensityGramContraction_nonnegative {Ω : Type} [Fintype Ω]
    (b d : Nat) (weight : Ω → ℚ) (hw : ∀ root, 0 ≤ weight root)
    (density : Ω → Fin d → ℚ) (pairDensity : Fin d → Fin d → ℚ)
    (hproduct : ∀ i j, pairDensity i j =
      ∑ root, weight root * density root i * density root j) :
    0 ≤ densityGramContraction Generated.certificate b d pairDensity /
      (Generated.certificate.scale : ℚ) := by
  exact div_nonneg
    (actual_densityGramContraction_nonnegative b d weight hw density pairDensity hproduct)
    (Nat.cast_nonneg _)

end InducedPentagons.Paper

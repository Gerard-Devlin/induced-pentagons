import InducedPentagonsPaper.PrimitiveColumnAlgebra
import InducedPentagonsPaper.PentagonSubsetCount

/-! The target primitive in the supplied certificate counts labelled induced
pentagons, hence ten times the induced vertex subsets. -/

open scoped BigOperators

namespace InducedPentagons.Paper

theorem primitivePentagon_satisfies_iff {n : Nat} (g : Graph (Fin n)) (f : Fin 5 → Fin n) :
    PatternSatisfies primitivePattern01 g f ↔ IsInducedPentagon g f := by
  constructor
  · intro hp i j
    rcases hp with ⟨he, hn⟩
    simp only [primitivePattern01, List.mem_cons, forall_eq_or_imp] at he hn
    rcases he with ⟨h01, h04, h12, h23, h34, _⟩
    rcases hn with ⟨h02, h03, h13, h14, h24, _⟩
    fin_cases i <;> fin_cases j <;> norm_num [cycleAdj]
    all_goals first | assumption | exact g.loopless _ | (rwa [g.symmetric])
  · intro hp
    constructor
    · intro e he
      rcases e with ⟨i, j⟩
      rw [hp]
      have hh : ∀ e ∈ primitivePattern01.edges, cycleAdj e.1 e.2 = true := by decide +kernel
      exact hh (i, j) he
    · intro e he
      rcases e with ⟨i, j⟩
      rw [hp]
      have hh : ∀ e ∈ primitivePattern01.nonedges, cycleAdj e.1 e.2 = false := by decide +kernel
      exact hh (i, j) he

def primitivePentagonEquiv {n : Nat} (g : Graph (Fin n)) :
    PatternInjection primitivePattern01 g ≃ PentagonEmbedding g where
  toFun f := ⟨f.val, (primitivePentagon_satisfies_iff g f.val).mp f.property.2⟩
  invFun f := ⟨f.val, inducedPentagon_injective f.property,
    (primitivePentagon_satisfies_iff g f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem primitivePentagon_count {n : Nat} (g : Graph (Fin n)) :
    patternInjectionCount primitivePattern01 g = Fintype.card (PentagonEmbedding g) :=
  Fintype.card_congr (primitivePentagonEquiv g)

theorem primitivePentagon_count_eq_ten_subsets {n : Nat} (g : Graph (Fin n)) :
    patternInjectionCount primitivePattern01 g = 10 * Fintype.card (PentagonSets g) := by
  rw [primitivePentagon_count, pentagon_card_eq_labelled_length,
    labelled_length_eq_ten_mul_normalized, pentagonSet_card_eq_normalized_length]


theorem primitivePentagon_density {n : Nat} (g : Graph (Fin n)) :
    patternInjectionDensity primitivePattern01 g =
      (10 * Fintype.card (PentagonSets g) : ℚ) / (n.descFactorial 5 : ℚ) := by
  rw [patternInjectionDensity, primitivePentagon_count_eq_ten_subsets]
  push_cast
  rfl

theorem primitivePentagon_density_seven (g : Graph (Fin 7)) :
    patternInjectionDensity primitivePattern01 g =
      (Fintype.card (PentagonSets g) : ℚ) / 252 := by
  rw [primitivePentagon_density]
  norm_num [Nat.descFactorial]
  ring

theorem primitive_target_entry {n : Nat} (g : Graph (Fin n)) :
    (primitiveSemanticDensities primitivePatternSpecs g)[1]! =
      patternInjectionDensity primitivePattern01 g := by
  rfl

theorem certificate_target_density (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    rowPrimitiveDensity h 1 =
      (Fintype.card (PentagonSets (maskGraph 7 h.mask)) : ℚ) / 252 := by
  have ht := primitive_certificate_density_entry h hh (⟨1, by decide⟩ : Fin 22)
  change patternInjectionDensity primitivePattern01 (maskGraph 7 h.mask) =
    rowPrimitiveDensity h 1 at ht
  rw [← ht]
  exact primitivePentagon_density_seven _

theorem certificate_hostLeft_pentagon_count (h : HostRow)
    (hh : h ∈ primitiveCertificateRows) :
    (hostLeft Generated.certificate h : ℚ) / 557383680 =
      ((5 / 663552 : ℚ) -
        (Fintype.card (PentagonSets (maskGraph 7 h.mask)) : ℚ) / 252) *
      (Generated.certificate.scale : ℚ) := by
  rw [primitive_hostLeft_normalized, certificate_target_density h hh]

theorem primitivePentagon_weight {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) :
    patternInjectionWeight primitivePattern01 g x = 10 * pentagonMass g x := by
  have h := Fintype.sum_equiv (primitivePentagonEquiv g)
    (fun f => ∏ i, x (f.val i)) (fun f => ∏ i, x (f.val i)) (fun _ => rfl)
  unfold patternInjectionWeight pentagonMass
  rw [h]
  ring

end InducedPentagons.Paper


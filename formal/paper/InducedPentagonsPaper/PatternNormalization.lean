import InducedPentagonsPaper.PatternEnumeration
import Mathlib.Data.Fintype.CardEmbedding

/-! Injection denominators and their probability normalization. -/

namespace InducedPentagons.Paper

def unconstrainedPattern (k : Nat) : PartialPattern k := ⟨[], []⟩

def unconstrainedPatternEquiv {k n : Nat} (g : Graph (Fin n)) :
    PatternInjection (unconstrainedPattern k) g ≃ (Fin k ↪ Fin n) where
  toFun f := ⟨f.val, f.property.1⟩
  invFun f := ⟨f, f.injective, by simp [PatternSatisfies, unconstrainedPattern]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem unconstrainedPattern_count {k n : Nat} (g : Graph (Fin n)) :
    patternInjectionCount (unconstrainedPattern k) g = n.descFactorial k := by
  rw [patternInjectionCount, Fintype.card_congr (unconstrainedPatternEquiv g)]
  simp

theorem patternInjectionCount_le_total {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    patternInjectionCount p g ≤ n.descFactorial k := by
  have h := Fintype.card_le_of_injective
    (fun f : PatternInjection p g => (⟨f.val, f.property.1⟩ : Fin k ↪ Fin n)) (by
      intro f h he
      apply Subtype.ext
      funext i
      exact congrArg (fun q : Fin k ↪ Fin n => q i) he)
  simpa [patternInjectionCount] using h

def patternInjectionDensity {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) : ℚ :=
  (patternInjectionCount p g : ℚ) / (n.descFactorial k : ℚ)

theorem patternInjectionDensity_nonnegative {k n : Nat} (p : PartialPattern k)
    (g : Graph (Fin n)) : 0 ≤ patternInjectionDensity p g := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem patternInjectionDensity_le_one {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    patternInjectionDensity p g ≤ 1 := by
  unfold patternInjectionDensity
  by_cases hd : n.descFactorial k = 0
  · simp [hd]
  · have hp : (0 : ℚ) < (n.descFactorial k : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    apply (div_le_one hp).mpr
    exact_mod_cast patternInjectionCount_le_total p g

end InducedPentagons.Paper

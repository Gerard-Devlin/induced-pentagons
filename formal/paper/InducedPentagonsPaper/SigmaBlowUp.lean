import InducedPentagonsPaper.WeightedApproximation
import InducedPentagonsPaper.WeightedClique

/-! Exact pentagon counting in blow-ups with variable integral class sizes,
and the reduction from finite unweighted inequalities to real weighted ones. -/

open scoped BigOperators

namespace InducedPentagons.Paper

def pentagonSigmaEquiv {V : Type} (g : Graph V) (m : V → ℕ) :
    PentagonEmbedding (sigmaBlowUp g m) ≃
      Σ p : PentagonEmbedding g, (i : Fin 5) → Fin (m (p.val i)) where
  toFun p := ⟨⟨fun i => (p.val i).1, p.property⟩, fun i => (p.val i).2⟩
  invFun p := ⟨fun i => ⟨p.1.val i, p.2 i⟩, p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable section

variable {V : Type} [Fintype V]

theorem natCast_pentagon_card_sigma (g : Graph V) (m : V → ℕ) :
    (Fintype.card (PentagonEmbedding (sigmaBlowUp g m)) : ℝ) =
      10 * pentagonMass g (fun v => (m v : ℝ)) := by
  rw [Fintype.card_congr (pentagonSigmaEquiv g m), Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin, Nat.cast_sum, Nat.cast_prod]
  unfold pentagonMass
  ring

theorem edgeMass_sigmaBlowUp_unit (g : Graph V) (m : V → ℕ) :
    edgeMass (sigmaBlowUp g m) (fun _ => 1) =
      edgeMass g (fun v => (m v : ℝ)) := by
  rw [edgeMass_unit, natCast_dart_card_sigma]
  ring

theorem pentagonMass_sigmaBlowUp_unit (g : Graph V) (m : V → ℕ) :
    pentagonMass (sigmaBlowUp g m) (fun _ => 1) =
      pentagonMass g (fun v => (m v : ℝ)) := by
  rw [pentagonMass_unit, natCast_pentagon_card_sigma]
  ring

/-- An unweighted inequality on the variable-size integral blow-ups of a fixed
base graph extends to all nonnegative real weights on that graph. -/
theorem squared_pentagon_bound_of_sigmaBlowUp (g : Graph V) (c : ℝ)
    (hblow : ∀ m : V → ℕ,
      pentagonMass (sigmaBlowUp g m) (fun _ => 1) ^ 2 ≤
        c * edgeMass (sigmaBlowUp g m) (fun _ => 1) ^ 5)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    pentagonMass g x ^ 2 ≤ c * edgeMass g x ^ 5 := by
  apply squared_pentagon_bound_of_integral g c _ hx
  intro m
  simpa only [pentagonMass_sigmaBlowUp_unit, edgeMass_sigmaBlowUp_unit] using hblow m

/-- Universal unweighted finite-graph bounds imply universal weighted bounds. -/
theorem squared_pentagon_bound_of_unweighted (c : ℝ)
    (hunweighted : ∀ (W : Type) [Fintype W] (h : Graph W),
      pentagonMass h (fun _ => 1) ^ 2 ≤ c * edgeMass h (fun _ => 1) ^ 5)
    (g : Graph V) {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    pentagonMass g x ^ 2 ≤ c * edgeMass g x ^ 5 :=
  squared_pentagon_bound_of_sigmaBlowUp g c
    (fun m => hunweighted (Σ v, Fin (m v)) (sigmaBlowUp g m)) hx

end
end InducedPentagons.Paper

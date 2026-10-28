import InducedPentagonsPaper.WeightedGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Analysis.SpecificLimits.Basic

/-! The weighted clique inequality, derived from finite Turán by integral
blow-ups and a limit of rounded nonnegative weights. -/

open scoped BigOperators Topology
open Filter

namespace InducedPentagons.Paper

def sigmaBlowUp {V : Type} (g : Graph V) (m : V → Nat) : Graph (Σ v, Fin (m v)) where
  adj u v := g.adj u.1 v.1
  symmetric u v := g.symmetric u.1 v.1
  loopless u := g.loopless u.1

def dartSigmaEquiv {V : Type} (g : Graph V) (m : V → Nat) :
    Darts (sigmaBlowUp g m) ≃ Σ p : Darts g, Fin (m p.val.1) × Fin (m p.val.2) where
  toFun p := ⟨⟨(p.val.1.1, p.val.2.1), p.property⟩, (p.val.1.2, p.val.2.2)⟩
  invFun p := ⟨(⟨p.1.val.1, p.2.1⟩, ⟨p.1.val.2, p.2.2⟩), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def mathlibDartEquiv {V : Type} (g : Graph V) : Darts g ≃ (toSimpleGraph g).Dart where
  toFun p := ⟨p.val, p.property⟩
  invFun p := ⟨p.toProd, p.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cliqueFree_comap {V W : Type*} {G : SimpleGraph V} {n : Nat}
    (hG : G.CliqueFree n) (f : W → V) : (G.comap f).CliqueFree n := by
  classical
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  let t : (⊤ : SimpleGraph (Fin n)) →g G :=
    { toFun := fun i => f (e i)
      map_rel' := fun h => e.map_rel_iff.mpr h }
  exact (t.toCopy (SimpleGraph.Hom.injective_of_top_hom t)).isContained.not_cliqueFree hG

noncomputable section

theorem natCast_dart_card_sigma {V : Type} [Fintype V] (g : Graph V) (m : V → Nat) :
    (Fintype.card (Darts (sigmaBlowUp g m)) : ℝ) =
      2 * edgeMass g (fun v => (m v : ℝ)) := by
  rw [Fintype.card_congr (dartSigmaEquiv g m), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_sum, Nat.cast_mul]
  unfold edgeMass
  ring

/-- Integral-weight form of the weighted clique inequality. -/
theorem integral_weighted_clique {V : Type} [Fintype V] (g : Graph V)
    {r : Nat} (hr : 1 ≤ r) (hG : (toSimpleGraph g).CliqueFree (r + 1)) (m : V → Nat) :
    2 * (r : ℝ) * edgeMass g (fun v => (m v : ℝ)) ≤
      ((r : ℝ) - 1) * (∑ v, (m v : ℝ)) ^ 2 := by
  classical
  let H := toSimpleGraph (sigmaBlowUp g m)
  have hH : H.CliqueFree (r + 1) := cliqueFree_comap hG Sigma.fst
  have hc : Fintype.card (Darts (sigmaBlowUp g m)) = 2 * H.edgeFinset.card := by
    rw [Fintype.card_congr (mathlibDartEquiv (sigmaBlowUp g m))]
    exact H.dart_card_eq_twice_card_edges
  have hT : r * Fintype.card (Darts (sigmaBlowUp g m)) ≤
      (r - 1) * Fintype.card (Σ v, Fin (m v)) ^ 2 := by
    rw [hc]
    calc
      r * (2 * H.edgeFinset.card) = 2 * r * H.edgeFinset.card := by ring
      _ ≤ 2 * r * SimpleGraph.turanNumber (Fintype.card (Σ v, Fin (m v))) r :=
        Nat.mul_le_mul_left _ hH.card_edgeFinset_le
      _ ≤ _ := SimpleGraph.mul_turanNumber_le
  have hR : (r : ℝ) * (Fintype.card (Darts (sigmaBlowUp g m)) : ℝ) ≤
      ((r : ℝ) - 1) * (Fintype.card (Σ v, Fin (m v)) : ℝ) ^ 2 := by
    exact_mod_cast hT
  rw [natCast_dart_card_sigma, Fintype.card_sigma] at hR
  simpa [Fintype.card_fin, Nat.cast_sum, mul_assoc, mul_comm, mul_left_comm] using hR

theorem scaled_integral_weighted_clique {V : Type} [Fintype V] (g : Graph V)
    {r : Nat} (hr : 1 ≤ r) (hG : (toSimpleGraph g).CliqueFree (r + 1))
    (m : V → Nat) (a : ℝ) :
    2 * (r : ℝ) * edgeMass g (fun v => a * (m v : ℝ)) ≤
      ((r : ℝ) - 1) * (∑ v, a * (m v : ℝ)) ^ 2 := by
  rw [edgeMass_scale, ← Finset.mul_sum, mul_pow]
  convert mul_le_mul_of_nonneg_left (integral_weighted_clique g hr hG m) (sq_nonneg a)
    using 1 <;> ring

/-- Motzkin--Straus upper bound for arbitrary nonnegative real vertex weights.
The proof uses integral blow-ups, finite Turán, and rounded-weight convergence. -/
theorem weighted_clique {V : Type} [Fintype V] (g : Graph V)
    {r : Nat} (hr : 1 ≤ r) (hG : (toSimpleGraph g).CliqueFree (r + 1))
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    2 * (r : ℝ) * edgeMass g x ≤ ((r : ℝ) - 1) * (∑ v, x v) ^ 2 := by
  let w : ℕ → V → ℝ := fun n v => (n : ℝ)⁻¹ * (⌊x v * (n : ℝ)⌋₊ : ℝ)
  have hw : ∀ v, Tendsto (fun n => w n v) atTop (𝓝 (x v)) := by
    intro v
    simpa only [Function.comp_def, w, div_eq_mul_inv, mul_comm] using
      (tendsto_nat_floor_mul_div_atTop (hx v)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hE : Tendsto (fun n => edgeMass g (w n)) atTop (𝓝 (edgeMass g x)) := by
    unfold edgeMass
    exact (tendsto_finsetSum Finset.univ (fun p _ =>
      (hw p.val.1).mul (hw p.val.2))).div_const 2
  have hS : Tendsto (fun n => ∑ v, w n v) atTop (𝓝 (∑ v, x v)) :=
    tendsto_finsetSum Finset.univ (fun v _ => hw v)
  have hbound : ∀ n, 2 * (r : ℝ) * edgeMass g (w n) ≤
      ((r : ℝ) - 1) * (∑ v, w n v) ^ 2 := fun n =>
    scaled_integral_weighted_clique g hr hG (fun v => ⌊x v * (n : ℝ)⌋₊) (n : ℝ)⁻¹
  exact le_of_tendsto_of_tendsto (Tendsto.const_mul _ hE)
    (Tendsto.const_mul _ (hS.pow 2)) (Eventually.of_forall hbound)

end
end InducedPentagons.Paper

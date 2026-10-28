import InducedPentagonsPaper.FiniteGraph
import InducedPentagons.Isolates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Weighted finite graph semantics. The factors 1/2 and 1/10 remove the
orientations of edges and the automorphisms of the induced pentagon. -/

open scoped BigOperators

namespace InducedPentagons.Paper

def Darts {V : Type} (g : Graph V) := {p : V × V // g.adj p.1 p.2 = true}

instance {V : Type} [Fintype V] (g : Graph V) : Fintype (Darts g) :=
  inferInstanceAs (Fintype {p : V × V // g.adj p.1 p.2 = true})

instance {V : Type} [Fintype V] (g : Graph V) : Fintype (PentagonEmbedding g) :=
  inferInstanceAs (Fintype {p : Fin 5 → V //
    ∀ i j, g.adj (p i) (p j) = cycleAdj i j})

def dartBlowUpEquiv {V W : Type} (g : Graph V) :
    Darts (blowUp g W) ≃ Darts g × (W × W) where
  toFun p := (⟨(p.val.1.1, p.val.2.1), p.property⟩, (p.val.1.2, p.val.2.2))
  invFun p := ⟨((p.1.val.1, p.2.1), (p.1.val.2, p.2.2)), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pentagonBlowUpEquiv {V W : Type} (g : Graph V) :
    PentagonEmbedding (blowUp g W) ≃ PentagonEmbedding g × (Fin 5 → W) where
  toFun p := (projectPentagon p, fun i => (p.val i).2)
  invFun p := liftPentagon p.1 p.2
  left_inv := lift_projectPentagon
  right_inv p := by
    apply Prod.ext
    · exact project_liftPentagon p.1 p.2
    · exact clone_liftPentagon p.1 p.2

theorem dart_card_blowUp {V W : Type} [Fintype V] [Fintype W] (g : Graph V) :
    Fintype.card (Darts (blowUp g W)) =
      Fintype.card (Darts g) * Fintype.card W ^ 2 := by
  rw [Fintype.card_congr (dartBlowUpEquiv g), Fintype.card_prod, Fintype.card_prod]
  ring

theorem pentagon_card_blowUp {V W : Type} [Fintype V] [Fintype W] (g : Graph V) :
    Fintype.card (PentagonEmbedding (blowUp g W)) =
      Fintype.card (PentagonEmbedding g) * Fintype.card W ^ 5 := by
  simp [Fintype.card_congr (pentagonBlowUpEquiv (W := W) g)]

def pentagonIsolatesEquiv {V W : Type} (g : Graph V) :
    PentagonEmbedding (withIsolates g W) ≃ PentagonEmbedding g where
  toFun := removeIsolatesPentagon
  invFun := addIsolatesPentagon
  left_inv := add_removeIsolatesPentagon
  right_inv := remove_addIsolatesPentagon

theorem pentagon_card_withIsolates {V W : Type} [Fintype V] [Fintype W]
    (g : Graph V) :
    Fintype.card (PentagonEmbedding (withIsolates g W)) =
      Fintype.card (PentagonEmbedding g) :=
  Fintype.card_congr (pentagonIsolatesEquiv g)

noncomputable section

def edgeMass {V : Type} [Fintype V] (g : Graph V) (x : V → ℝ) : ℝ :=
  (∑ p : Darts g, x p.val.1 * x p.val.2) / 2

def pentagonMass {V : Type} [Fintype V] (g : Graph V) (x : V → ℝ) : ℝ :=
  (∑ p : PentagonEmbedding g, ∏ i, x (p.val i)) / 10

theorem edgeMass_nonnegative {V : Type} [Fintype V] (g : Graph V)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) : 0 ≤ edgeMass g x := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (hx _) (hx _))

theorem pentagonMass_nonnegative {V : Type} [Fintype V] (g : Graph V)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) : 0 ≤ pentagonMass g x := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun p _ => Finset.prod_nonneg (fun i _ => hx _))

theorem edgeMass_scale {V : Type} [Fintype V] (g : Graph V)
    (x : V → ℝ) (r : ℝ) :
    edgeMass g (fun v => r * x v) = r ^ 2 * edgeMass g x := by
  unfold edgeMass
  have h : ∀ p : Darts g, (r * x p.val.1) * (r * x p.val.2) =
      r ^ 2 * (x p.val.1 * x p.val.2) := fun p => by ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

theorem pentagonMass_scale {V : Type} [Fintype V] (g : Graph V)
    (x : V → ℝ) (r : ℝ) :
    pentagonMass g (fun v => r * x v) = r ^ 5 * pentagonMass g x := by
  unfold pentagonMass
  simp_rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum]
  ring

theorem edgeMass_unit {V : Type} [Fintype V] (g : Graph V) :
    edgeMass g (fun _ => 1) = (Fintype.card (Darts g) : ℝ) / 2 := by
  simp [edgeMass]

theorem pentagonMass_unit {V : Type} [Fintype V] (g : Graph V) :
    pentagonMass g (fun _ => 1) = (Fintype.card (PentagonEmbedding g) : ℝ) / 10 := by
  simp [pentagonMass]

def classMass {V W : Type} [Fintype W] (x : V × W → ℝ) (v : V) : ℝ :=
  ∑ w, x (v, w)

/-- Collapsing clone classes preserves the weighted edge polynomial. -/
theorem edgeMass_blowUp {V W : Type} [Fintype V] [Fintype W]
    (g : Graph V) (x : V × W → ℝ) :
    edgeMass (blowUp g W) x = edgeMass g (classMass x) := by
  unfold edgeMass
  congr 1
  rw [Fintype.sum_equiv (dartBlowUpEquiv g)
    (fun p => x p.val.1 * x p.val.2)
    (fun p => x (p.1.val.1, p.2.1) * x (p.1.val.2, p.2.2)) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.sum_prod_type]
  exact (Fintype.sum_mul_sum (fun u => x (p.val.1, u))
    (fun v => x (p.val.2, v))).symm

/-- Every induced pentagon uses distinct base classes. Summing over its clone
choices therefore gives the product of the five class masses. -/
theorem pentagonMass_blowUp {V W : Type} [Fintype V] [Fintype W]
    (g : Graph V) (x : V × W → ℝ) :
    pentagonMass (blowUp g W) x = pentagonMass g (classMass x) := by
  unfold pentagonMass
  congr 1
  rw [Fintype.sum_equiv (pentagonBlowUpEquiv g)
    (fun p => ∏ i, x (p.val i))
    (fun p => ∏ i, x (p.1.val i, p.2 i)) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  exact (Fintype.prod_sum (fun i w => x (p.val i, w))).symm

theorem pentagonMass_withIsolates {V W : Type} [Fintype V] [Fintype W]
    (g : Graph V) (x : Sum V W → ℝ) :
    pentagonMass (withIsolates g W) x = pentagonMass g (fun v => x (.inl v)) := by
  unfold pentagonMass
  congr 1
  exact (Fintype.sum_equiv (pentagonIsolatesEquiv g).symm
    (fun p => ∏ i, x (.inl (p.val i)))
    (fun p => ∏ i, x (p.val i)) (fun _ => rfl)).symm

def squaredRatio {V : Type} [Fintype V] (g : Graph V) (x : V → ℝ) : ℝ :=
  pentagonMass g x ^ 2 / edgeMass g x ^ 5

theorem squaredRatio_scale {V : Type} [Fintype V] (g : Graph V)
    (x : V → ℝ) {r : ℝ} (hr : r ≠ 0) :
    squaredRatio g (fun v => r * x v) = squaredRatio g x := by
  unfold squaredRatio
  rw [pentagonMass_scale, edgeMass_scale]
  have hn : (r ^ 5 * pentagonMass g x) ^ 2 = r ^ 10 * pentagonMass g x ^ 2 := by ring
  have hd : (r ^ 2 * edgeMass g x) ^ 5 = r ^ 10 * edgeMass g x ^ 5 := by ring
  rw [hn, hd, mul_div_mul_left _ _ (pow_ne_zero 10 hr)]

theorem squaredRatio_blowUp {V W : Type} [Fintype V] [Fintype W]
    (g : Graph V) (x : V × W → ℝ) :
    squaredRatio (blowUp g W) x = squaredRatio g (classMass x) := by
  simp only [squaredRatio, pentagonMass_blowUp, edgeMass_blowUp]

theorem clebsch_dart_card : Fintype.card (Darts clebsch) = 80 := by decide +kernel

theorem clebsch_edgeMass_unit : edgeMass clebsch (fun _ => 1) = 40 := by
  rw [edgeMass_unit, clebsch_dart_card]
  norm_num

theorem clebsch_balanced_edgeMass (k : ℝ) :
    edgeMass clebsch (fun _ => k) = 40 * k ^ 2 := by
  simpa [clebsch_edgeMass_unit, mul_comm] using
    edgeMass_scale clebsch (fun _ => 1) k

theorem clebsch_blowUp_edges {W : Type} [Fintype W] :
    edgeMass (blowUp clebsch W) (fun _ => 1) = 40 * (Fintype.card W : ℝ) ^ 2 := by
  rw [edgeMass_blowUp]
  have h : classMass (fun _ : Fin 16 × W => (1 : ℝ)) =
      fun _ => (Fintype.card W : ℝ) := by
    funext v
    simp [classMass]
  rw [h, clebsch_balanced_edgeMass]

end

end InducedPentagons.Paper

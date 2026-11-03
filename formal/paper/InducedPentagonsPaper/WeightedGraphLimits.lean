import InducedPentagonsPaper.WeightedGraph
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

/-! Continuity, limits, and finite-dimensional attainment for weighted graph
polynomials. These results concern a fixed finite graph; they do not assert
compactness or attainment in the graphon space. -/

open scoped BigOperators Topology
open Filter Set

noncomputable section

namespace InducedPentagons.Paper

variable {V : Type} [Fintype V]

theorem continuous_edgeMass (g : Graph V) : Continuous (edgeMass g) := by
  unfold edgeMass
  fun_prop

theorem continuous_pentagonMass (g : Graph V) : Continuous (pentagonMass g) := by
  unfold pentagonMass
  fun_prop

theorem continuousAt_squaredRatio (g : Graph V) {x : V → ℝ}
    (hx : edgeMass g x ≠ 0) : ContinuousAt (squaredRatio g) x := by
  exact ((continuous_pentagonMass g).continuousAt.pow 2).div
    ((continuous_edgeMass g).continuousAt.pow 5) (pow_ne_zero 5 hx)

theorem tendsto_edgeMass (g : Graph V) {α : Type*} {l : Filter α}
    {x : α → V → ℝ} {w : V → ℝ}
    (hx : ∀ v, Tendsto (fun a => x a v) l (𝓝 (w v))) :
    Tendsto (fun a => edgeMass g (x a)) l (𝓝 (edgeMass g w)) :=
  (continuous_edgeMass g).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hx)

theorem tendsto_pentagonMass (g : Graph V) {α : Type*} {l : Filter α}
    {x : α → V → ℝ} {w : V → ℝ}
    (hx : ∀ v, Tendsto (fun a => x a v) l (𝓝 (w v))) :
    Tendsto (fun a => pentagonMass g (x a)) l (𝓝 (pentagonMass g w)) :=
  (continuous_pentagonMass g).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hx)

theorem tendsto_squaredRatio (g : Graph V) {α : Type*} {l : Filter α}
    {x : α → V → ℝ} {w : V → ℝ} (hw : edgeMass g w ≠ 0)
    (hx : ∀ v, Tendsto (fun a => x a v) l (𝓝 (w v))) :
    Tendsto (fun a => squaredRatio g (x a)) l (𝓝 (squaredRatio g w)) :=
  (continuousAt_squaredRatio g hw).tendsto.comp (tendsto_pi_nhds.mpr hx)

/-- Nonnegative vertex weights with total mass one. -/
def unitMassWeights (V : Type) [Fintype V] : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1}

theorem unitMassWeights_coordinate_le_one {x : V → ℝ}
    (hx : x ∈ unitMassWeights V) (v : V) : x v ≤ 1 := by
  calc
    x v ≤ ∑ u, x u := Finset.single_le_sum (fun u _ => hx.1 u) (Finset.mem_univ v)
    _ = 1 := hx.2

theorem isClosed_unitMassWeights : IsClosed (unitMassWeights V) := by
  have hn : IsClosed {x : V → ℝ | ∀ v, 0 ≤ x v} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun v : V => isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply v))
  have hs : IsClosed {x : V → ℝ | ∑ v, x v = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hn.inter hs

theorem isCompact_unitMassWeights : IsCompact (unitMassWeights V) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_unitMassWeights
  intro x hx
  exact ⟨hx.1, fun v => unitMassWeights_coordinate_le_one hx v⟩

/-- Fixing the edge mass cuts out a compact subset of the weight simplex. -/
theorem isCompact_unitMassWeights_edgeMass (g : Graph V) (e : ℝ) :
    IsCompact {x ∈ unitMassWeights V | edgeMass g x = e} :=
  isCompact_unitMassWeights.inter_right
    (isClosed_eq (continuous_edgeMass g) continuous_const)

/-- Any feasible edge mass on a fixed finite graph has a pentagon maximizer. -/
theorem exists_max_pentagonMass (g : Graph V) (e : ℝ)
    (hfeasible : ∃ x ∈ unitMassWeights V, edgeMass g x = e) :
    ∃ x ∈ unitMassWeights V, edgeMass g x = e ∧
      ∀ y ∈ unitMassWeights V, edgeMass g y = e →
        pentagonMass g y ≤ pentagonMass g x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_unitMassWeights_edgeMass g e).exists_isMaxOn
    hfeasible (continuous_pentagonMass g).continuousOn
  exact ⟨x, hx.1, hx.2, fun y hy he => hmax ⟨hy, he⟩⟩

end InducedPentagons.Paper

import InducedPentagonsPaper.WeightedClique
import InducedPentagonsPaper.IndependentSets

namespace InducedPentagons.Paper

def graphComplement {V : Type} [DecidableEq V] (g : Graph V) : Graph V where
  adj u v := decide (u ≠ v) && !(g.adj u v)
  symmetric u v := by simp only [ne_comm, g.symmetric u v]
  loopless u := by simp

theorem toSimpleGraph_complement {V : Type} [DecidableEq V] (g : Graph V) :
    toSimpleGraph (graphComplement g) = (toSimpleGraph g)ᶜ := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  simp [toSimpleGraph_adj, graphComplement, SimpleGraph.compl_adj]

/-- The weighted complement bound used in Lemma 11.1, for arbitrary
nonnegative weights, without an assumed independence-number inequality. -/
theorem clebsch_complement_weighted {x : Fin 16 → ℝ} (hx : ∀ v, 0 ≤ x v) :
    6 * edgeMass (graphComplement clebsch) x ≤
      (12 / 5 : ℝ) * (∑ v, x v) ^ 2 := by
  have hG : (toSimpleGraph (graphComplement clebsch)).CliqueFree (5 + 1) := by
    rw [toSimpleGraph_complement]
    exact clebsch_complement_cliqueFree
  have h := weighted_clique (graphComplement clebsch) (by norm_num : 1 ≤ 5) hG hx
  norm_num at h
  linarith

end InducedPentagons.Paper

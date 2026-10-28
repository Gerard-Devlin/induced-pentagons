import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import InducedPentagons.FiniteGraph

/-! A Mathlib interpretation of the independently checked finite graph model. -/

namespace InducedPentagons.Paper

def toSimpleGraph {V : Type} (g : Graph V) : SimpleGraph V where
  Adj u v := g.adj u v = true
  symm := ⟨by
    intro u v h
    simpa only [g.symmetric u v] using h⟩
  loopless := ⟨by
    intro v
    simp only [g.loopless v, Bool.false_eq_true, not_false_eq_true]⟩

@[simp] theorem toSimpleGraph_adj {V : Type} (g : Graph V) (u v : V) :
    (toSimpleGraph g).Adj u v ↔ g.adj u v = true := Iff.rfl

end InducedPentagons.Paper

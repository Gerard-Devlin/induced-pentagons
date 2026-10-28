import InducedPentagonsPaper.AtlasCertificate
import InducedPentagonsPaper.PatternSemantics

/-! Atlas coverage for Mathlib graphs and reduction of arbitrary partial-pattern counts. -/

namespace InducedPentagons.Paper

noncomputable def boolGraphOfSimpleGraph {V : Type} (g : SimpleGraph V) : Graph V := by
  classical
  exact {
    adj := fun u v => decide (g.Adj u v)
    symmetric := by intro u v; simp only [g.adj_comm u v]
    loopless := by intro u; simp
  }

theorem toSimpleGraph_boolGraphOfSimpleGraph {V : Type} (g : SimpleGraph V) :
    toSimpleGraph (boolGraphOfSimpleGraph g) = g := by
  classical
  apply SimpleGraph.ext
  funext u v
  apply propext
  simp [toSimpleGraph, boolGraphOfSimpleGraph]

theorem seven_vertex_simpleGraph_isomorphic_to_certificate_host (g : SimpleGraph (Fin 7)) :
    ∃ m ∈ Generated.certificate.hosts.toList,
      Nonempty (g ≃g toSimpleGraph (maskGraph 7 m)) := by
  have h := seven_vertex_graph_isomorphic_to_certificate_host (boolGraphOfSimpleGraph g)
  rw [toSimpleGraph_boolGraphOfSimpleGraph] at h
  exact h

theorem patternInjectionCount_reduced_to_certificate {k : Nat} (p : PartialPattern k)
    (g : Graph (Fin 7)) :
    ∃ m ∈ Generated.certificate.hosts.toList,
      patternInjectionCount p g = patternInjectionCount p (maskGraph 7 m) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := atlas7_covers g
  refine ⟨m, ?_, patternInjectionCount_isomorphic p e⟩
  rw [← atlas7_eq_certificate_hosts]
  exact hm

end InducedPentagons.Paper

import InducedPentagonsPaper.RootedClassification
import InducedPentagonsPaper.PrimitiveTable

/-! Exact pattern-count signatures can certify pairwise nonisomorphism. -/

namespace InducedPentagons.Paper

def patternSignatureSeparationCheck (data : List (Nat × List Nat)) : Bool :=
  data.all (fun r => data.all (fun s => decide (r.2 = s.2 → r.1 = s.1)))

theorem patternSignatureSeparationCheck_sound {n roots : Nat}
    (specs : List PrimitivePatternSpec) (basis : List Nat) (data : List (Nat × List Nat))
    (hm : data.map Prod.fst = basis)
    (hs : ∀ r ∈ data, primitiveSemanticCounts specs (maskGraph n r.1) = r.2)
    (hc : patternSignatureSeparationCheck data = true) :
    RootedFlagBasisSeparated n roots basis := by
  intro a ha b hb ⟨e⟩
  rw [← hm] at ha hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  obtain ⟨s, hmem, rfl⟩ := List.mem_map.mp hb
  have he := primitiveSemanticCounts_isomorphic specs e.graphEquiv
  rw [hs r hr, hs s hmem] at he
  exact (of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp hc) r hr)) s hmem)) he

end InducedPentagons.Paper

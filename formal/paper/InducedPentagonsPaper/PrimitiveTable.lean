import InducedPentagonsPaper.PrimitiveFast
import InducedPentagonsPaper.PatternNormalization
import InducedPentagonsPaper.AtlasInterpretation

/-! Transfer a fully checked table of primitive counts to arbitrary seven-vertex graphs. -/

namespace InducedPentagons.Paper

theorem primitiveSemanticCounts_isomorphic (specs : List PrimitivePatternSpec)
    {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    primitiveSemanticCounts specs g = primitiveSemanticCounts specs h := by
  unfold primitiveSemanticCounts
  apply List.map_congr_left
  intro p _
  exact patternInjectionCount_isomorphic p.pattern e

def primitiveSemanticDensities (specs : List PrimitivePatternSpec) {n : Nat}
    (g : Graph (Fin n)) : List ℚ :=
  specs.map (fun p => patternInjectionDensity p.pattern g)

theorem primitiveSemanticDensities_eq_zipWith (specs : List PrimitivePatternSpec)
    {n : Nat} (g : Graph (Fin n)) :
    primitiveSemanticDensities specs g =
      List.zipWith (fun c d : Nat => (c : ℚ) / (d : ℚ))
        (primitiveSemanticCounts specs g) (specs.map (fun p => n.descFactorial p.vertices)) := by
  simp only [primitiveSemanticDensities, primitiveSemanticCounts, List.zipWith_map,
    List.zipWith_self, patternInjectionDensity]

theorem primitiveSemanticDensities_isomorphic (specs : List PrimitivePatternSpec)
    {n : Nat} {g h : Graph (Fin n)} (e : BooleanGraphEquiv g h) :
    primitiveSemanticDensities specs g = primitiveSemanticDensities specs h := by
  rw [primitiveSemanticDensities_eq_zipWith, primitiveSemanticDensities_eq_zipWith,
    primitiveSemanticCounts_isomorphic specs e]

theorem primitiveSemanticDensities_bounds (specs : List PrimitivePatternSpec)
    {n : Nat} (g : Graph (Fin n)) :
    ∀ d ∈ primitiveSemanticDensities specs g, 0 ≤ d ∧ d ≤ 1 := by
  intro d hd
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hd
  exact ⟨patternInjectionDensity_nonnegative p.pattern g,
    patternInjectionDensity_le_one p.pattern g⟩

theorem primitive_counts_reduced_to_verified_rows (specs : List PrimitivePatternSpec)
    (rows : List HostRow)
    (hm : rows.map HostRow.mask = Generated.certificate.hosts.toList)
    (hc : ∀ h ∈ rows, h.primitive.toList =
      primitiveSemanticCounts specs (maskGraph 7 h.mask)) (g : Graph (Fin 7)) :
    ∃ h ∈ rows, Nonempty (BooleanGraphEquiv g (maskGraph 7 h.mask)) ∧
      primitiveSemanticCounts specs g = h.primitive.toList := by
  obtain ⟨m, hmem, ⟨e⟩⟩ := atlas7_covers g
  rw [atlas7_eq_certificate_hosts, ← hm] at hmem
  obtain ⟨h, hh, heq⟩ := List.mem_map.mp hmem
  subst m
  exact ⟨h, hh, ⟨e⟩, (primitiveSemanticCounts_isomorphic specs e).trans (hc h hh).symm⟩

end InducedPentagons.Paper

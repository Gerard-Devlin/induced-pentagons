import InducedPentagonsPaper.PrimitiveTable
import InducedPentagonsPaper.Generated.PrimitiveComplete

/-! All primitive entries in the actual certificate rows have finite graph semantics. -/

namespace InducedPentagons.Paper

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem primitive_certificate_rows_masks :
    primitiveCertificateRows.map HostRow.mask = Generated.certificate.hosts.toList := by
  decide +kernel

theorem primitive_certificate_rows_indices :
    primitiveCertificateRows.map HostRow.index = List.range 1044 := by
  decide +kernel

theorem primitive_certificate_rows_count : primitiveCertificateRows.length = 1044 := by
  have h := congrArg List.length primitive_certificate_rows_masks
  simpa only [List.length_map, Array.length_toList, certificate_host_count] using h

theorem primitive_certificate_rows_masks_nodup :
    (primitiveCertificateRows.map HostRow.mask).Nodup := by
  rw [primitive_certificate_rows_masks, ← atlas7_eq_certificate_hosts]
  exact atlas7_masks_nodup

theorem primitive_certificate_row_width (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.primitive.size = 22 := by
  have hw := congrArg List.length (primitive_certificate_rows_semantics h hh)
  simpa only [Array.length_toList, primitiveSemanticCounts, List.length_map,
    primitivePatternSpecs_count] using hw

theorem primitive_certificate_densities (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    primitiveSemanticDensities primitivePatternSpecs (maskGraph 7 h.mask) =
      List.zipWith (fun c d : Nat => (c : ℚ) / (d : ℚ))
        h.primitive.toList expectedPatternDenominators.toList := by
  rw [primitiveSemanticDensities_eq_zipWith,
    ← primitive_certificate_rows_semantics h hh, primitivePattern_denominators]

theorem primitive_counts_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows, Nonempty (BooleanGraphEquiv g (maskGraph 7 h.mask)) ∧
      primitiveSemanticCounts primitivePatternSpecs g = h.primitive.toList :=
  primitive_counts_reduced_to_verified_rows primitivePatternSpecs primitiveCertificateRows
    primitive_certificate_rows_masks primitive_certificate_rows_semantics g

theorem primitive_densities_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows,
      primitiveSemanticDensities primitivePatternSpecs g =
        List.zipWith (fun c d : Nat => (c : ℚ) / (d : ℚ))
          h.primitive.toList expectedPatternDenominators.toList := by
  obtain ⟨h, hh, ⟨e⟩, _⟩ := primitive_counts_on_all_seven_vertex_graphs g
  exact ⟨h, hh, (primitiveSemanticDensities_isomorphic primitivePatternSpecs e).trans
    (primitive_certificate_densities h hh)⟩

theorem primitive_counts_on_all_seven_vertex_simpleGraphs (g : SimpleGraph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows,
      Nonempty (g ≃g toSimpleGraph (maskGraph 7 h.mask)) ∧
      primitiveSemanticCounts primitivePatternSpecs (boolGraphOfSimpleGraph g) =
        h.primitive.toList := by
  obtain ⟨h, hh, ⟨e⟩, hc⟩ := primitive_counts_on_all_seven_vertex_graphs (boolGraphOfSimpleGraph g)
  refine ⟨h, hh, ?_, hc⟩
  have he := e.toSimpleGraphIso
  rw [toSimpleGraph_boolGraphOfSimpleGraph] at he
  exact ⟨he⟩

end InducedPentagons.Paper

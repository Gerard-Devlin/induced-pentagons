import InducedPentagonsPaper.Generated.CensusComplete
import InducedPentagonsPaper.AtlasCensusIsomorphism
import InducedPentagonsPaper.AtlasInterpretation

/-! The complete stored census supplies counts on every seven-vertex graph. -/
namespace InducedPentagons.Paper

theorem atlas_census_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ r ∈ atlasCensusRows,
      Nonempty (toSimpleGraph g ≃g toSimpleGraph (maskGraph 7 r.mask)) ∧
      Nat.card (toSimpleGraph g ≃g toSimpleGraph g) = r.automorphisms ∧
      Nat.card (CensusIsoClass (toSimpleGraph g)) = r.orbit := by
  obtain ⟨m, hm, ⟨e⟩⟩ := seven_vertex_graph_isomorphic_to_certificate_host g
  rw [← atlas_census_hosts] at hm
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  have hc := atlas_census_semantics r hr
  exact ⟨r, hr, ⟨e⟩, (census_automorphisms_isomorphic e).trans hc.1,
    (census_orbit_isomorphic e).trans hc.2⟩

theorem atlas_census_on_all_seven_vertex_simpleGraphs (g : SimpleGraph (Fin 7)) :
    ∃ r ∈ atlasCensusRows,
      Nonempty (g ≃g toSimpleGraph (maskGraph 7 r.mask)) ∧
      Nat.card (g ≃g g) = r.automorphisms ∧
      Nat.card (CensusIsoClass g) = r.orbit := by
  simpa only [toSimpleGraph_boolGraphOfSimpleGraph] using
    atlas_census_on_all_seven_vertex_graphs (boolGraphOfSimpleGraph g)

end InducedPentagons.Paper

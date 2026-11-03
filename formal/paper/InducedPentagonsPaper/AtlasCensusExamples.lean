import InducedPentagonsPaper.AtlasOrbit
namespace InducedPentagons.Paper
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem census_empty_automorphisms :
    Nat.card (toSimpleGraph (maskGraph 7 0) ≃g toSimpleGraph (maskGraph 7 0)) = 5040 := by
  rw [← censusAutomorphismCount_semantics]
  decide +kernel

theorem census_single_edge_automorphisms :
    Nat.card (toSimpleGraph (maskGraph 7 1) ≃g toSimpleGraph (maskGraph 7 1)) = 240 := by
  rw [← censusAutomorphismCount_semantics]
  decide +kernel

theorem census_middle_automorphisms :
    Nat.card (toSimpleGraph (maskGraph 7 42479) ≃g toSimpleGraph (maskGraph 7 42479)) = 4 := by
  rw [← censusAutomorphismCount_semantics]
  decide +kernel

theorem census_empty_orbit : Nat.card (CensusIsoClass (toSimpleGraph (maskGraph 7 0))) = 1 := by
  rw [census_orbit_card, censusAutomorphismCount_semantics, census_empty_automorphisms]
  decide +kernel

theorem census_single_edge_orbit :
    Nat.card (CensusIsoClass (toSimpleGraph (maskGraph 7 1))) = 21 := by
  rw [census_orbit_card, censusAutomorphismCount_semantics, census_single_edge_automorphisms]
  decide +kernel

theorem census_middle_orbit :
    Nat.card (CensusIsoClass (toSimpleGraph (maskGraph 7 42479))) = 1260 := by
  rw [census_orbit_card, censusAutomorphismCount_semantics, census_middle_automorphisms]
  decide +kernel

end InducedPentagons.Paper

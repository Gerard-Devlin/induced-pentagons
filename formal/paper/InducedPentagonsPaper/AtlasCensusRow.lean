import InducedPentagonsPaper.AtlasOrbit

/-! Soundness of stored automorphism/orbit census rows. -/
namespace InducedPentagons.Paper

structure AtlasCensusRow where
  mask : Nat
  automorphisms : Nat
  orbit : Nat
  deriving Repr, DecidableEq

def atlasCensusRowCheck (r : AtlasCensusRow) : Bool :=
  decide (censusAutomorphismCount (maskGraph 7 r.mask) = r.automorphisms) &&
    decide (r.automorphisms * r.orbit = 5040)

theorem atlasCensusRowCheck_sound (r : AtlasCensusRow)
    (hr : atlasCensusRowCheck r = true) :
    Nat.card (toSimpleGraph (maskGraph 7 r.mask) ≃g
      toSimpleGraph (maskGraph 7 r.mask)) = r.automorphisms ∧
    Nat.card (CensusIsoClass (toSimpleGraph (maskGraph 7 r.mask))) = r.orbit := by
  simp only [atlasCensusRowCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at hr
  constructor
  · rw [← censusAutomorphismCount_semantics]
    exact hr.1
  · rw [census_orbit_card, hr.1]
    change 5040 / r.automorphisms = r.orbit
    rw [← hr.2, Nat.mul_comm, Nat.mul_div_cancel _]
    rw [← hr.1]
    exact censusAutomorphismCount_pos _

end InducedPentagons.Paper

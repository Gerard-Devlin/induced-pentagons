import InducedPentagonsPaper.AtlasOrbit

/-! Automorphism and labelled orbit counts are invariant under graph isomorphism. -/
namespace InducedPentagons.Paper

noncomputable def censusAutomorphismIsoEquiv {n : Nat} {g h : SimpleGraph (Fin n)}
    (e : g ≃g h) : (g ≃g g) ≃ (h ≃g h) where
  toFun a := (e.symm.trans a).trans e
  invFun a := (e.trans a).trans e.symm
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

theorem census_automorphisms_isomorphic {n : Nat} {g h : SimpleGraph (Fin n)}
    (e : g ≃g h) : Nat.card (g ≃g g) = Nat.card (h ≃g h) :=
  Nat.card_congr (censusAutomorphismIsoEquiv e)

theorem censusAutomorphismCount_isomorphic {n : Nat} {g h : Graph (Fin n)}
    (e : toSimpleGraph g ≃g toSimpleGraph h) :
    censusAutomorphismCount g = censusAutomorphismCount h := by
  rw [censusAutomorphismCount_semantics, censusAutomorphismCount_semantics]
  exact census_automorphisms_isomorphic e

theorem census_orbit_isomorphic {n : Nat} {g h : Graph (Fin n)}
    (e : toSimpleGraph g ≃g toSimpleGraph h) :
    Nat.card (CensusIsoClass (toSimpleGraph g)) =
      Nat.card (CensusIsoClass (toSimpleGraph h)) := by
  rw [census_orbit_card, census_orbit_card, censusAutomorphismCount_isomorphic e]

end InducedPentagons.Paper

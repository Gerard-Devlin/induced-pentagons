import InducedPentagonsPaper.AtlasCensus
import Mathlib.Data.Fintype.Perm

/-! Orbit sizes as cardinalities of labelled isomorphism classes. -/

namespace InducedPentagons.Paper

/-- Every target graph together with a chosen isomorphism from `g`. -/
def CensusIsoTotal {n : Nat} (g : SimpleGraph (Fin n)) :=
  Σ h : SimpleGraph (Fin n), g ≃g h

/-- Forgetting the target graph and keeping the vertex permutation loses no information. -/
noncomputable def censusIsoTotalEquiv {n : Nat} (g : SimpleGraph (Fin n)) :
    CensusIsoTotal g ≃ Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun x => x.2.toEquiv) (by
    constructor
    · rintro ⟨h, e⟩ ⟨k, f⟩ hef
      have hgraph : h = k := by
        apply SimpleGraph.ext
        funext a b
        apply propext
        obtain ⟨i, rfl⟩ := e.surjective a
        obtain ⟨j, rfl⟩ := e.surjective b
        have hi : e i = f i := congrArg (fun q : Equiv.Perm (Fin n) => q i) hef
        have hj : e j = f j := congrArg (fun q : Equiv.Perm (Fin n) => q j) hef
        exact e.map_rel_iff.trans (by rw [hi, hj]; exact f.map_rel_iff.symm)
      subst k
      have he : e = f := RelIso.ext (fun i => congrArg (fun q : Equiv.Perm (Fin n) => q i) hef)
      subst f
      rfl
    · intro e
      exact ⟨⟨g.map e, SimpleGraph.Iso.map e g⟩, rfl⟩)

/-- The labelled isomorphism class of a graph, without a selected isomorphism. -/
def CensusIsoClass {n : Nat} (g : SimpleGraph (Fin n)) :=
  {h : SimpleGraph (Fin n) // Nonempty (g ≃g h)}

noncomputable def censusIsoClassRepresentative {n : Nat} {g : SimpleGraph (Fin n)}
    (h : CensusIsoClass g) : g ≃g h.val := Classical.choice h.property

noncomputable def censusIsoClassProdEquiv {n : Nat} (g : SimpleGraph (Fin n)) :
    CensusIsoClass g × (g ≃g g) ≃ CensusIsoTotal g where
  toFun x := ⟨x.1.val, x.2.trans (censusIsoClassRepresentative x.1)⟩
  invFun x := (⟨x.1, ⟨x.2⟩⟩, x.2.trans (censusIsoClassRepresentative ⟨x.1, ⟨x.2⟩⟩).symm)
  left_inv x := by
    apply Prod.ext
    · rfl
    · ext i
      simp [censusIsoClassRepresentative]
  right_inv x := by
    rcases x with ⟨h, e⟩
    change (⟨h, (e.trans (censusIsoClassRepresentative ⟨h, ⟨e⟩⟩).symm).trans
      (censusIsoClassRepresentative ⟨h, ⟨e⟩⟩)⟩ : CensusIsoTotal g) = ⟨h, e⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    apply RelIso.ext
    intro i
    simp

theorem census_orbit_mul_automorphisms {n : Nat} (g : SimpleGraph (Fin n)) :
    Nat.card (CensusIsoClass g) * Nat.card (g ≃g g) = n.factorial := by
  rw [← Nat.card_prod,
    Nat.card_congr ((censusIsoClassProdEquiv g).trans (censusIsoTotalEquiv g)),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem census_orbit_card {n : Nat} (g : Graph (Fin n)) :
    Nat.card (CensusIsoClass (toSimpleGraph g)) =
      n.factorial / censusAutomorphismCount g := by
  have hm := census_orbit_mul_automorphisms (toSimpleGraph g)
  rw [← censusAutomorphismCount_semantics] at hm
  rw [← hm, Nat.mul_div_cancel _ (censusAutomorphismCount_pos g)]

end InducedPentagons.Paper






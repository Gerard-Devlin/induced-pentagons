import InducedPentagonsPaper.Generated.FixedTypeData

/-! The actual 34 fixed-density masks classify every five-vertex graph uniquely. -/

namespace InducedPentagons.Paper

def fiveGraphType (g : Graph (Fin 5)) : Nat := rootedClassify 10 fixedTypeLookup g

theorem fiveGraphType_sound (g : Graph (Fin 5)) :
    fiveGraphType g ∈ fixedTypeMasks ∧
      Nonempty (BooleanGraphEquiv g (maskGraph 5 (fiveGraphType g))) := by
  obtain ⟨hm, ⟨e⟩⟩ := rootedClassify_sound edgeIndexSeparated_five edgeIndexBounded_five
    fixed_type_lookup_checked g (rootTypeCheck_zero 0 g)
  exact ⟨hm, ⟨e.graphEquiv⟩⟩

theorem fiveGraphType_eq_iff (g : Graph (Fin 5)) (m : Nat) (hm : m ∈ fixedTypeMasks) :
    fiveGraphType g = m ↔ Nonempty (toSimpleGraph g ≃g toSimpleGraph (maskGraph 5 m)) := by
  constructor
  · intro he
    obtain ⟨_, ⟨e⟩⟩ := fiveGraphType_sound g
    rw [he] at e
    exact ⟨e.toSimpleGraphIso⟩
  · rintro ⟨e⟩
    exact (rootedClassify_eq_iff edgeIndexSeparated_five edgeIndexBounded_five
      fixed_type_lookup_checked fixed_types_separated g (rootTypeCheck_zero 0 g) m hm).mpr
      ⟨(BooleanGraphEquiv.ofSimpleGraphIso e).rootedZero⟩

theorem fiveGraphType_isomorphic {g h : Graph (Fin 5)} (e : BooleanGraphEquiv g h) :
    fiveGraphType g = fiveGraphType h :=
  rootedClassify_isomorphic edgeIndexSeparated_five edgeIndexBounded_five
    fixed_type_lookup_checked fixed_types_separated (rootTypeCheck_zero 0 g)
    (rootTypeCheck_zero 0 h) e.rootedZero

theorem fiveGraphType_certificate_mem (g : Graph (Fin 5)) :
    fiveGraphType g ∈ Generated.certificate.fixedMasks.toList := by
  rw [← fixed_type_masks_certificate]
  exact (fiveGraphType_sound g).1

theorem fixed_type_certificate_separated :
    RootedFlagBasisSeparated 5 0 Generated.certificate.fixedMasks.toList := by
  rw [← fixed_type_masks_certificate]
  exact fixed_types_separated

end InducedPentagons.Paper

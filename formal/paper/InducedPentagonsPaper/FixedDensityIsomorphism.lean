import InducedPentagonsPaper.FixedDensity

/-! Fixed induced-subset counts and complementary-edge counts are graph invariants. -/

namespace InducedPentagons.Paper

def inducedImageIso {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) (s : Finset (Fin n)) :
    (toSimpleGraph g).induce (s : Set (Fin n)) ≃g
      (toSimpleGraph h).induce (s.image e.val : Set (Fin m)) where
  toEquiv := e.val.imageFinset s
  map_rel_iff' := by
    intro i j
    change h.adj (e.val i.val) (e.val j.val) = true ↔ g.adj i.val j.val = true
    rw [e.property]

theorem inducedGraphTypeSet_image_iff {n m k : Nat} (t : Graph (Fin k))
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h)
    (s : Finset (Fin n)) :
    InducedGraphTypeSet t h (s.image e.val) ↔ InducedGraphTypeSet t g s := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.trans (inducedImageIso e s).symm⟩
  · rintro ⟨f⟩
    exact ⟨f.trans (inducedImageIso e s)⟩

theorem complementEdge_image_iff {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) (s : Finset (Fin n)) :
    (∃ u v : Fin m, u ∉ s.image e.val ∧ v ∉ s.image e.val ∧ h.adj u v = true) ↔
      ∃ u v : Fin n, u ∉ s ∧ v ∉ s ∧ g.adj u v = true := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    refine ⟨e.val.symm u, e.val.symm v, ?_, ?_, ?_⟩
    · intro hm
      exact hu (Finset.mem_image.mpr ⟨_, hm, e.val.apply_symm_apply u⟩)
    · intro hm
      exact hv (Finset.mem_image.mpr ⟨_, hm, e.val.apply_symm_apply v⟩)
    · have he := e.property (e.val.symm u) (e.val.symm v)
      simp only [Equiv.apply_symm_apply] at he
      exact he.symm.trans huv
  · rintro ⟨u, v, hu, hv, huv⟩
    refine ⟨e.val u, e.val v, ?_, ?_, (e.property u v).trans huv⟩
    · rintro hm
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hm
      exact hu ((e.val.injective heq) ▸ hw)
    · rintro hm
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hm
      exact hv ((e.val.injective heq) ▸ hw)

def inducedTypeSetEquiv {n m k : Nat} (t : Graph (Fin k))
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    {s : Finset (Fin n) // InducedGraphTypeSet t g s} ≃
      {s : Finset (Fin m) // InducedGraphTypeSet t h s} where
  toFun s := ⟨s.val.image e.val, (inducedGraphTypeSet_image_iff t e s.val).mpr s.property⟩
  invFun s := ⟨s.val.image e.val.symm, (inducedGraphTypeSet_image_iff t e.symm s.val).mpr s.property⟩
  left_inv s := by apply Subtype.ext; simp [Finset.image_image]
  right_inv s := by apply Subtype.ext; simp [Finset.image_image]

def inducedTypeComplementEquiv {n m k : Nat} (t : Graph (Fin k))
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    {s : Finset (Fin n) // InducedGraphTypeSet t g s ∧
      ∃ u v : Fin n, u ∉ s ∧ v ∉ s ∧ g.adj u v = true} ≃
    {s : Finset (Fin m) // InducedGraphTypeSet t h s ∧
      ∃ u v : Fin m, u ∉ s ∧ v ∉ s ∧ h.adj u v = true} where
  toFun s := ⟨s.val.image e.val,
    (inducedGraphTypeSet_image_iff t e s.val).mpr s.property.1,
    (complementEdge_image_iff e s.val).mpr s.property.2⟩
  invFun s := ⟨s.val.image e.val.symm,
    (inducedGraphTypeSet_image_iff t e.symm s.val).mpr s.property.1,
    (complementEdge_image_iff e.symm s.val).mpr s.property.2⟩
  left_inv s := by apply Subtype.ext; simp [Finset.image_image]
  right_inv s := by apply Subtype.ext; simp [Finset.image_image]

theorem inducedTypeSetCount_isomorphic {n m k : Nat} (t : Graph (Fin k))
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    inducedTypeSetCount t g = inducedTypeSetCount t h := by
  classical
  exact Fintype.card_congr (inducedTypeSetEquiv t e)

theorem inducedTypeComplementCount_isomorphic {n m k : Nat} (t : Graph (Fin k))
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    inducedTypeComplementCount t g = inducedTypeComplementCount t h := by
  classical
  exact Fintype.card_congr (inducedTypeComplementEquiv t e)

theorem fixedDensityCount_isomorphic {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) (t : Nat) (ht : t ∈ fixedTypeMasks) :
    fixedDensityCount g t = fixedDensityCount h t := by
  rw [fixedDensityCount_semantics g t ht, fixedDensityCount_semantics h t ht]
  exact inducedTypeSetCount_isomorphic _ e

theorem fixedComplementCount_isomorphic {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) (t : Nat) (ht : t ∈ fixedTypeMasks) :
    fixedComplementCount g t = fixedComplementCount h t := by
  rw [fixedComplementCount_semantics g t ht, fixedComplementCount_semantics h t ht]
  exact inducedTypeComplementCount_isomorphic _ e

theorem fixedDensityCounts_isomorphic {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) : fixedDensityCounts g = fixedDensityCounts h := by
  apply List.map_congr_left
  intro t ht
  exact fixedDensityCount_isomorphic e t ht

theorem fixedComplementCounts_isomorphic {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) : fixedComplementCounts g = fixedComplementCounts h := by
  apply List.map_congr_left
  intro t ht
  exact fixedComplementCount_isomorphic e t ht

end InducedPentagons.Paper

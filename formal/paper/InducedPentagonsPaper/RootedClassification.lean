import InducedPentagonsPaper.RootedFlagSeparation

/-! A checked lookup table classifies graphs independently of their free-vertex labels. -/

namespace InducedPentagons.Paper

def rootedLookupCheck (n bits roots typeMask : Nat) (basis : List Nat)
    (lookup : Fin (2 ^ bits) → RootedFlagWitness) : Bool :=
  (List.finRange (2 ^ bits)).all (fun m =>
    if rootTypeCheck roots typeMask (maskGraph n m.val) then
      decide ((lookup m).source = m.val) && rootedFlagRowCheck n roots basis (lookup m)
    else true)

def rootedClassify {n : Nat} (bits : Nat)
    (lookup : Fin (2 ^ bits) → RootedFlagWitness) (g : Graph (Fin n)) : Nat :=
  (lookup (graphEncoding bits g)).target

theorem rootedClassify_sound {n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    {basis : List Nat} {lookup : Fin (2 ^ bits) → RootedFlagWitness}
    (hc : rootedLookupCheck n bits roots typeMask basis lookup = true)
    (g : Graph (Fin n)) (hg : rootTypeCheck roots typeMask g = true) :
    rootedClassify bits lookup g ∈ basis ∧
      Nonempty (RootedGraphEquiv roots g (maskGraph n (rootedClassify bits lookup g))) := by
  let m := graphEncoding bits g
  have hm : rootTypeCheck roots typeMask (maskGraph n m.val) = true := by
    simpa only [rootTypeCheck, m, graphEncoding_adj hs hb g] using hg
  have h := (List.all_eq_true.mp hc) m (by simp)
  simp only [hm, if_true, Bool.and_eq_true_iff, decide_eq_true_eq,
    rootedFlagRowCheck, List.contains_iff_mem] at h
  obtain ⟨e⟩ := rootedWitnessCheck_sound h.2.2
  have he : RootedGraphEquiv roots g (maskGraph n (lookup m).source) := {
    graphEquiv := ⟨Equiv.refl _, by
      intro i j
      rw [h.1]
      exact graphEncoding_adj hs hb g i j⟩
    fixed := fun _ _ => rfl
  }
  exact ⟨h.2.1, ⟨he.trans e⟩⟩

theorem rootedClassify_eq_iff {n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    {basis : List Nat} {lookup : Fin (2 ^ bits) → RootedFlagWitness}
    (hc : rootedLookupCheck n bits roots typeMask basis lookup = true)
    (hp : RootedFlagBasisSeparated n roots basis)
    (g : Graph (Fin n)) (hg : rootTypeCheck roots typeMask g = true)
    (m : Nat) (hm : m ∈ basis) :
    rootedClassify bits lookup g = m ↔
      Nonempty (RootedGraphEquiv roots g (maskGraph n m)) := by
  obtain ⟨hmem, ⟨e⟩⟩ := rootedClassify_sound hs hb hc g hg
  constructor
  · rintro rfl
    exact ⟨e⟩
  · rintro ⟨f⟩
    exact hp _ hmem m hm ⟨e.symm.trans f⟩

theorem rootedClassify_isomorphic {n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    {basis : List Nat} {lookup : Fin (2 ^ bits) → RootedFlagWitness}
    (hc : rootedLookupCheck n bits roots typeMask basis lookup = true)
    (hp : RootedFlagBasisSeparated n roots basis)
    {g h : Graph (Fin n)} (hg : rootTypeCheck roots typeMask g = true)
    (hh : rootTypeCheck roots typeMask h = true) (e : RootedGraphEquiv roots g h) :
    rootedClassify bits lookup g = rootedClassify bits lookup h := by
  obtain ⟨hmem, ⟨f⟩⟩ := rootedClassify_sound hs hb hc h hh
  exact (rootedClassify_eq_iff hs hb hc hp g hg _ hmem).mpr ⟨e.trans f⟩

def BooleanGraphEquiv.ofSimpleGraphIso {V W : Type} {g : Graph V} {h : Graph W}
    (e : toSimpleGraph g ≃g toSimpleGraph h) : BooleanGraphEquiv g h :=
  ⟨e.toEquiv, fun _i _j => Bool.eq_iff_iff.mpr e.map_rel_iff⟩

def BooleanGraphEquiv.rootedZero {n : Nat} {g h : Graph (Fin n)}
    (e : BooleanGraphEquiv g h) : RootedGraphEquiv 0 g h :=
  ⟨e, fun i hi => by omega⟩

@[simp] theorem rootTypeCheck_zero {n : Nat} (typeMask : Nat) (g : Graph (Fin n)) :
    rootTypeCheck 0 typeMask g = true := by
  simp [rootTypeCheck]

end InducedPentagons.Paper

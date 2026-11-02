import InducedPentagonsPaper.GraphEncoding

/-! Root-preserving graph equivalences and sound finite flag-basis coverage checks. -/

namespace InducedPentagons.Paper

structure RootedGraphEquiv (roots : Nat) {n : Nat} (g h : Graph (Fin n)) where
  graphEquiv : BooleanGraphEquiv g h
  fixed : ∀ i : Fin n, i.val < roots → graphEquiv.val i = i

def RootedGraphEquiv.trans {roots n : Nat} {g h k : Graph (Fin n)}
    (e : RootedGraphEquiv roots g h) (f : RootedGraphEquiv roots h k) :
    RootedGraphEquiv roots g k where
  graphEquiv := e.graphEquiv.trans f.graphEquiv
  fixed i hi := by
    change f.graphEquiv.val (e.graphEquiv.val i) = i
    rw [e.fixed i hi, f.fixed i hi]

def RootedGraphEquiv.symm {roots n : Nat} {g h : Graph (Fin n)}
    (e : RootedGraphEquiv roots g h) : RootedGraphEquiv roots h g where
  graphEquiv := e.graphEquiv.symm
  fixed i hi := by
    change e.graphEquiv.val.symm i = i
    apply e.graphEquiv.val.injective
    rw [Equiv.apply_symm_apply, e.fixed i hi]

def rootTypeCheck {n : Nat} (roots typeMask : Nat) (g : Graph (Fin n)) : Bool :=
  decide (∀ i j : Fin n, i.val < roots → j.val < roots →
    g.adj i j = (maskGraph n typeMask).adj i j)

def rootedWitnessMap (n code : Nat) (i : Fin n) : Fin n :=
  ⟨((code / 8 ^ i.val) % 8) % n, Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

def rootedWitnessCheck (n roots source target code : Nat) : Bool :=
  decide (Function.Injective (rootedWitnessMap n code)) &&
  decide (∀ i : Fin n, i.val < roots → rootedWitnessMap n code i = i) &&
  decide (∀ i j : Fin n,
    (maskGraph n target).adj (rootedWitnessMap n code i) (rootedWitnessMap n code j) =
      (maskGraph n source).adj i j)

theorem rootedWitnessCheck_sound {n roots source target code : Nat}
    (hw : rootedWitnessCheck n roots source target code = true) :
    Nonempty (RootedGraphEquiv roots (maskGraph n source) (maskGraph n target)) := by
  simp only [rootedWitnessCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at hw
  exact ⟨{
    graphEquiv := ⟨Equiv.ofBijective (rootedWitnessMap n code)
      ⟨hw.1.1, Finite.surjective_of_injective hw.1.1⟩, hw.2⟩
    fixed := hw.1.2
  }⟩

structure RootedFlagWitness where
  source : Nat
  target : Nat
  permutation : Nat

def rootedFlagRowCheck (n roots : Nat) (basis : List Nat) (w : RootedFlagWitness) : Bool :=
  basis.contains w.target && rootedWitnessCheck n roots w.source w.target w.permutation

def RootedFlagBasisCovers (n roots typeMask : Nat) (basis : List Nat) : Prop :=
  ∀ g : Graph (Fin n), rootTypeCheck roots typeMask g = true →
    ∃ m ∈ basis, Nonempty (RootedGraphEquiv roots g (maskGraph n m))

theorem rootedFlagBasisCovers_of_rows {n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    (basis : List Nat) (rows : List RootedFlagWitness)
    (hr : rows.map RootedFlagWitness.source =
      (List.range (2 ^ bits)).filter (fun m => rootTypeCheck roots typeMask (maskGraph n m)))
    (hc : rows.all (rootedFlagRowCheck n roots basis) = true) :
    RootedFlagBasisCovers n roots typeMask basis := by
  intro g hg
  let encoded := graphEncoding bits g
  have henc : rootTypeCheck roots typeMask (maskGraph n encoded.val) = true := by
    simpa only [rootTypeCheck, encoded, graphEncoding_adj hs hb g] using hg
  have hm : encoded.val ∈ rows.map RootedFlagWitness.source := by
    rw [hr]
    exact List.mem_filter.mpr ⟨List.mem_range.mpr encoded.isLt, henc⟩
  obtain ⟨w, hw, heq⟩ := List.mem_map.mp hm
  have hcheck := (List.all_eq_true.mp hc) w hw
  simp only [rootedFlagRowCheck, Bool.and_eq_true_iff, List.contains_iff_mem] at hcheck
  obtain ⟨e⟩ := rootedWitnessCheck_sound hcheck.2
  have he : RootedGraphEquiv roots g (maskGraph n w.source) := {
    graphEquiv := ⟨Equiv.refl _, by
      intro i j
      rw [heq]
      exact graphEncoding_adj hs hb g i j⟩
    fixed := fun _ _ => rfl
  }
  exact ⟨w.target, hcheck.1, ⟨he.trans e⟩⟩

end InducedPentagons.Paper

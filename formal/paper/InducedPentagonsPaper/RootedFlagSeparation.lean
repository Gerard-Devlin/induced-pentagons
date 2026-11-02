import InducedPentagonsPaper.RootedFlags

/-! Exhaustive root-preserving permutations turn finite separation checks into uniqueness. -/

namespace InducedPentagons.Paper

def RootedPermutationCodesComplete (n roots : Nat) (codes : List Nat) : Prop :=
  ∀ f : Fin n → Fin n, Function.Injective f →
    (∀ i : Fin n, i.val < roots → f i = i) →
      ∃ code ∈ codes, rootedWitnessMap n code = f

def rootedBasisSeparatedCheck (n roots : Nat) (codes basis : List Nat) : Bool :=
  basis.all (fun a => basis.all (fun b => codes.all (fun code =>
    decide (rootedWitnessCheck n roots a b code = true → a = b))))

def RootedFlagBasisSeparated (n roots : Nat) (basis : List Nat) : Prop :=
  ∀ a ∈ basis, ∀ b ∈ basis,
    Nonempty (RootedGraphEquiv roots (maskGraph n a) (maskGraph n b)) → a = b

theorem rootedBasisSeparatedCheck_sound {n roots : Nat} {codes basis : List Nat}
    (hp : RootedPermutationCodesComplete n roots codes)
    (hc : rootedBasisSeparatedCheck n roots codes basis = true) :
    RootedFlagBasisSeparated n roots basis := by
  intro a ha b hb ⟨e⟩
  obtain ⟨code, hcode, he⟩ := hp e.graphEquiv.val e.graphEquiv.val.injective e.fixed
  have hcheck := (List.all_eq_true.mp ((List.all_eq_true.mp
    ((List.all_eq_true.mp hc) a ha)) b hb)) code hcode
  have hw : rootedWitnessCheck n roots a b code = true := by
    simp only [rootedWitnessCheck, he, Bool.and_eq_true_iff, decide_eq_true_eq]
    exact ⟨⟨e.graphEquiv.val.injective, e.fixed⟩, e.graphEquiv.property⟩
  exact (of_decide_eq_true hcheck) hw

end InducedPentagons.Paper

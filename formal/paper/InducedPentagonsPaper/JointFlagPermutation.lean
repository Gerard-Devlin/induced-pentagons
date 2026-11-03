import InducedPentagonsPaper.JointFlagSampling
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic

/-! Uniform full-permutation fibers of the joint flag sample space. -/

namespace InducedPentagons.Paper

abbrev JointFlagPositions (roots free : Nat) := Fin roots ⊕ (Fin free ⊕ Fin free)

namespace JointFlagSample

def orderedVertex {n roots free : Nat} (x : JointFlagSample n roots free)
    (l : Fin free ≃ x.left) (r : Fin free ≃ x.right) :
    JointFlagPositions roots free → Fin n :=
  Sum.elim x.1 (Sum.elim (fun i => (l i).val) (fun i => (r i).val))

theorem orderedVertex_injective {n roots free : Nat} (x : JointFlagSample n roots free)
    (l : Fin free ≃ x.left) (r : Fin free ≃ x.right) :
    Function.Injective (x.orderedVertex l r) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (x.1.injective hab)
  · rcases b with b | b
    · have ha : x.1 a ∈ flagRootVertices x.1 := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      have hb := (l b).property
      change x.1 a = (l b).val at hab
      rw [← hab] at hb
      exact False.elim (Finset.disjoint_left.mp x.roots_left_disjoint ha hb)
    · have ha : x.1 a ∈ flagRootVertices x.1 ∪ x.left :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
      have hb := Finset.mem_compl.mp (r b).property
      change x.1 a = (r b).val at hab
      exact False.elim (hb (hab ▸ ha))
  · exact False.elim (by
      rcases a with a | a
      · have hb : x.1 b ∈ flagRootVertices x.1 := Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
        have ha := (l a).property
        change (l a).val = x.1 b at hab
        rw [hab] at ha
        exact Finset.disjoint_left.mp x.roots_left_disjoint hb ha
      · have hb : x.1 b ∈ flagRootVertices x.1 ∪ x.left :=
          Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
        have ha := Finset.mem_compl.mp (r a).property
        change (r a).val = x.1 b at hab
        exact ha (hab.symm ▸ hb))
  · rcases a with a | a <;> rcases b with b | b
    · exact congrArg (fun i => Sum.inr (Sum.inl i)) (l.injective (Subtype.ext hab))
    · have ha : (l a).val ∈ flagRootVertices x.1 ∪ x.left := Finset.mem_union_right _ (l a).property
      have hb := Finset.mem_compl.mp (r b).property
      change (l a).val = (r b).val at hab
      exact False.elim (hb (hab ▸ ha))
    · have hb : (l b).val ∈ flagRootVertices x.1 ∪ x.left := Finset.mem_union_right _ (l b).property
      have ha := Finset.mem_compl.mp (r a).property
      change (r a).val = (l b).val at hab
      exact False.elim (ha (hab.symm ▸ hb))
    · exact congrArg (fun i => Sum.inr (Sum.inr i)) (r.injective (Subtype.ext hab))

noncomputable def orderedEquiv {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) (l : Fin free ≃ x.left) (r : Fin free ≃ x.right) :
    JointFlagPositions roots free ≃ Fin n :=
  Equiv.ofBijective (x.orderedVertex l r)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨x.orderedVertex_injective l r, by simp [JointFlagPositions, hn]; omega⟩)





def PermutationCompatible {n roots free : Nat} (x : JointFlagSample n roots free)
    (e : JointFlagPositions roots free ≃ Fin n) : Prop :=
  (∀ i, e (Sum.inl i) = x.1 i) ∧
    Finset.univ.image (fun i : Fin free => e (Sum.inr (Sum.inl i))) = x.left

theorem orderedEquiv_compatible {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) (l : Fin free ≃ x.left) (r : Fin free ≃ x.right) :
    x.PermutationCompatible (x.orderedEquiv hn l r) := by
  refine ⟨fun _ => rfl, ?_⟩
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  change (∃ i, (l i).val = v) ↔ v ∈ x.left
  constructor
  · rintro ⟨i, rfl⟩
    exact (l i).property
  · intro hv
    obtain ⟨i, hi⟩ := l.surjective ⟨v, hv⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem compatible_left_mem {n roots free : Nat} (x : JointFlagSample n roots free)
    (e : JointFlagPositions roots free ≃ Fin n) (he : x.PermutationCompatible e)
    (i : Fin free) : e (Sum.inr (Sum.inl i)) ∈ x.left := by
  rw [← he.2]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem compatible_right_mem {n roots free : Nat} (x : JointFlagSample n roots free)
    (e : JointFlagPositions roots free ≃ Fin n) (he : x.PermutationCompatible e)
    (i : Fin free) : e (Sum.inr (Sum.inr i)) ∈ x.right := by
  apply Finset.mem_compl.mpr
  intro hm
  rcases Finset.mem_union.mp hm with hr | hl
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
    have hc := e.injective ((he.1 j).trans hj)
    cases hc
  · rw [← he.2] at hl
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hl
    have hc := e.injective hj
    cases hc

noncomputable def compatibleLeftEquiv {n roots free : Nat} (x : JointFlagSample n roots free)
    (e : JointFlagPositions roots free ≃ Fin n) (he : x.PermutationCompatible e) :
    Fin free ≃ x.left :=
  Equiv.ofBijective (fun i => ⟨e (Sum.inr (Sum.inl i)), x.compatible_left_mem e he i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro a b hab
      exact Sum.inl.inj (Sum.inr.inj (e.injective (congrArg Subtype.val hab))), by
      simp only [Fintype.card_fin, Fintype.card_coe, x.left_card]⟩)

noncomputable def compatibleRightEquiv {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free)
    (e : JointFlagPositions roots free ≃ Fin n) (he : x.PermutationCompatible e) :
    Fin free ≃ x.right :=
  Equiv.ofBijective (fun i => ⟨e (Sum.inr (Sum.inr i)), x.compatible_right_mem e he i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro a b hab
      exact Sum.inr.inj (Sum.inr.inj (e.injective (congrArg Subtype.val hab))), by
      simp only [Fintype.card_fin, Fintype.card_coe, x.right_card hn]⟩)

noncomputable def permutationFiberEquiv {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) :
    {e : JointFlagPositions roots free ≃ Fin n // x.PermutationCompatible e} ≃
      (Fin free ≃ x.left) × (Fin free ≃ x.right) where
  toFun e := ⟨x.compatibleLeftEquiv e.val e.property,
    x.compatibleRightEquiv hn e.val e.property⟩
  invFun p := ⟨x.orderedEquiv hn p.1 p.2, x.orderedEquiv_compatible hn p.1 p.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rcases i with i | i
    · exact (e.property.1 i).symm
    · rcases i with i | i <;> rfl
  right_inv p := by
    apply Prod.ext <;> apply Equiv.ext <;> intro i <;> apply Subtype.ext <;> rfl

theorem permutationFiber_card {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) :
    Nat.card {e : JointFlagPositions roots free ≃ Fin n // x.PermutationCompatible e} =
      free.factorial ^ 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (x.permutationFiberEquiv hn), Fintype.card_prod,
    Fintype.card_equiv (x.left.orderIsoOfFin x.left_card).toEquiv,
    Fintype.card_equiv (x.right.orderIsoOfFin (x.right_card hn)).toEquiv,
    Fintype.card_fin, pow_two]




def ofPermutation {n roots free : Nat} (e : JointFlagPositions roots free ≃ Fin n) :
    JointFlagSample n roots free := by
  let f : Fin roots ↪ Fin n := ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩
  let s := Finset.univ.image (fun i : Fin free => e (Sum.inr (Sum.inl i)))
  refine ⟨f, s, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_compl.mpr
    intro hr
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
    have hc := e.injective hj
    cases hc
  · change (Finset.univ.image (fun i : Fin free => e (Sum.inr (Sum.inl i)))).card = free
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      exact Sum.inl.inj (Sum.inr.inj (e.injective hab)))]
    exact Finset.card_fin free

theorem ofPermutation_compatible {n roots free : Nat}
    (e : JointFlagPositions roots free ≃ Fin n) :
    (ofPermutation e).PermutationCompatible e := ⟨fun _ => rfl, rfl⟩

theorem ext_root_left {n roots free : Nat} {x y : JointFlagSample n roots free}
    (hr : x.1 = y.1) (hl : x.left = y.left) : x = y := by
  rcases x with ⟨xr, xl⟩
  rcases y with ⟨yr, yl⟩
  cases hr
  exact congrArg (Sigma.mk xr) (Subtype.ext hl)

theorem ofPermutation_eq_iff {n roots free : Nat} (x : JointFlagSample n roots free)
    (e : JointFlagPositions roots free ≃ Fin n) :
    ofPermutation e = x ↔ x.PermutationCompatible e := by
  constructor
  · intro h
    rw [← h]
    exact ofPermutation_compatible e
  · intro h
    apply ext_root_left
    · apply Function.Embedding.ext
      exact h.1
    · exact h.2

theorem ofPermutation_fiber_card {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) :
    Nat.card {e : JointFlagPositions roots free ≃ Fin n // ofPermutation e = x} =
      free.factorial ^ 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun e => ofPermutation_eq_iff x e)),
    x.permutationFiber_card hn]

theorem ofPermutation_predicate_card {n roots free : Nat} (hn : n = roots + 2 * free)
    (P : JointFlagSample n roots free → Prop) :
    Nat.card {e : JointFlagPositions roots free ≃ Fin n // P (ofPermutation e)} =
      Nat.card {x : JointFlagSample n roots free // P x} * free.factorial ^ 2 := by
  classical
  rw [← Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype ofPermutation (fun _ => Iff.rfl))]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [← Nat.card_eq_fintype_card, ofPermutation_fiber_card hn]
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, Nat.card_eq_fintype_card]

end JointFlagSample




/-- Roots are first, then the left extension, then the right extension. -/
def jointFlagPositionEquiv {n roots free : Nat} (hn : n = roots + 2 * free) :
    JointFlagPositions roots free ≃ Fin n :=
  ((Equiv.sumCongr (Equiv.refl (Fin roots)) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

def jointFlagFullPermutationEquiv {n roots free : Nat} (hn : n = roots + 2 * free) :
    Equiv.Perm (Fin n) ≃ (JointFlagPositions roots free ≃ Fin n) :=
  Equiv.equivCongr (jointFlagPositionEquiv hn).symm (Equiv.refl (Fin n))

/-- Forget the two free-block orderings in a full permutation. -/
def jointFlagSampleOfPermutation {n roots free : Nat} (hn : n = roots + 2 * free)
    (e : Equiv.Perm (Fin n)) : JointFlagSample n roots free :=
  JointFlagSample.ofPermutation (jointFlagFullPermutationEquiv hn e)

theorem jointFlagFullPermutation_fiber_card {n roots free : Nat}
    (hn : n = roots + 2 * free) (x : JointFlagSample n roots free) :
    Nat.card {e : Equiv.Perm (Fin n) // jointFlagSampleOfPermutation hn e = x} =
      free.factorial ^ 2 := by
  let E : {e : Equiv.Perm (Fin n) // jointFlagSampleOfPermutation hn e = x} ≃
      {e : JointFlagPositions roots free ≃ Fin n // JointFlagSample.ofPermutation e = x} :=
    (jointFlagFullPermutationEquiv hn).subtypeEquiv (fun _ => Iff.rfl)
  exact (Nat.card_congr E).trans (JointFlagSample.ofPermutation_fiber_card hn x)

theorem jointFlagFullPermutation_predicate_card {n roots free : Nat}
    (hn : n = roots + 2 * free) (P : JointFlagSample n roots free → Prop) :
    Nat.card {e : Equiv.Perm (Fin n) // P (jointFlagSampleOfPermutation hn e)} =
      Nat.card {x : JointFlagSample n roots free // P x} * free.factorial ^ 2 := by
  let E : {e : Equiv.Perm (Fin n) // P (jointFlagSampleOfPermutation hn e)} ≃
      {e : JointFlagPositions roots free ≃ Fin n // P (JointFlagSample.ofPermutation e)} :=
    (jointFlagFullPermutationEquiv hn).subtypeEquiv (fun _ => Iff.rfl)
  exact (Nat.card_congr E).trans (JointFlagSample.ofPermutation_predicate_card hn P)

theorem jointFlagFullPermutation_one_root_fiber_card (x : JointFlagSample 7 1 3) :
    Nat.card {e : Equiv.Perm (Fin 7) // jointFlagSampleOfPermutation (by decide) e = x} =
      36 := by
  rw [jointFlagFullPermutation_fiber_card]
  decide

theorem jointFlagFullPermutation_three_roots_fiber_card (x : JointFlagSample 7 3 2) :
    Nat.card {e : Equiv.Perm (Fin 7) // jointFlagSampleOfPermutation (by decide) e = x} =
      4 := by
  rw [jointFlagFullPermutation_fiber_card]
  decide

theorem jointFlagFullPermutation_pair_count {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) :
    Nat.card {e : Equiv.Perm (Fin n) //
      let x := jointFlagSampleOfPermutation hn e
      valid x.1 = true ∧ classify x = i ∧ classify (x.swap hn) = j} =
      jointFlagPairCount hn valid classify i j * free.factorial ^ 2 := by
  classical
  simpa only [jointFlagPairCount, Nat.card_eq_fintype_card] using
    (jointFlagFullPermutation_predicate_card hn (fun x =>
      valid x.1 = true ∧ classify x = i ∧ classify (x.swap hn) = j))





theorem jointFlagSample_card_mul_factorial_sq {n roots free : Nat}
    (hn : n = roots + 2 * free) :
    (n.descFactorial roots * (n - roots).choose free) * free.factorial ^ 2 = n.factorial := by
  classical
  have h := jointFlagFullPermutation_predicate_card hn (fun _ => True)
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm, jointFlagSample_card] using h.symm

/-- Uniform permutation sampling and uniform joint sampling give the same rational probability. -/
theorem jointFlagFullPermutation_probability {n roots free : Nat}
    (hn : n = roots + 2 * free) (P : JointFlagSample n roots free → Prop) :
    (Nat.card {e : Equiv.Perm (Fin n) // P (jointFlagSampleOfPermutation hn e)} : ℚ) /
      n.factorial =
    (Nat.card {x : JointFlagSample n roots free // P x} : ℚ) /
      (n.descFactorial roots * (n - roots).choose free) := by
  rw [jointFlagFullPermutation_predicate_card hn P,
    ← jointFlagSample_card_mul_factorial_sq hn]
  push_cast
  exact mul_div_mul_right _ _ (by positivity)

end InducedPentagons.Paper


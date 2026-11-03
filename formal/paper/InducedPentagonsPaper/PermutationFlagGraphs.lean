import InducedPentagonsPaper.JointFlagPermutation
import InducedPentagonsPaper.JointFlagGraphs

/-! Permutation block flags and sorted-subset flags are root-preservingly isomorphic. -/

namespace InducedPentagons.Paper

namespace JointFlagSample

/-- Relabel a freely ordered extension by the canonical sorted extension. -/
def orderingEquiv {n roots free : Nat} (x : JointFlagSample n roots free)
    (l : Fin free ≃ x.left) : Fin (roots + free) ≃ Fin (roots + free) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin roots))
    (l.trans (x.left.orderIsoOfFin x.left_card).toEquiv.symm))).trans finSumFinEquiv

theorem vertex_orderingEquiv {n roots free : Nat} (x : JointFlagSample n roots free)
    (l : Fin free ≃ x.left) (i : Fin (roots + free)) :
    x.vertex (x.orderingEquiv l i) = Fin.append x.1 (fun j => (l j).val) i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [orderingEquiv]
  · simp only [orderingEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, vertex_free,
      Fin.append_right, subsetVertex_eq_orderEmb]
    change (((x.left.orderIsoOfFin x.left_card).toEquiv)
      (((x.left.orderIsoOfFin x.left_card).toEquiv).symm (l j))).val = (l j).val
    rw [Equiv.apply_symm_apply]

def orderedGraphEquiv {n roots free : Nat} (x : JointFlagSample n roots free)
    (l : Fin free ≃ x.left) (g : Graph (Fin n)) :
    RootedGraphEquiv roots
      (comapBooleanGraph g (Fin.append x.1 (fun j => (l j).val))) (x.graph g) where
  graphEquiv := ⟨x.orderingEquiv l, by
    intro i j
    change g.adj (x.vertex (x.orderingEquiv l i)) (x.vertex (x.orderingEquiv l j)) = _
    rw [vertex_orderingEquiv, vertex_orderingEquiv]
    rfl⟩
  fixed i hi := by
    change x.orderingEquiv l i = i
    have he : i = (⟨i.val, hi⟩ : Fin roots).castAdd free := Fin.ext rfl
    have hroot (j : Fin roots) : x.orderingEquiv l (j.castAdd free) = j.castAdd free := by
      simp only [orderingEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply, finSumFinEquiv_apply_left]
    exact he ▸ hroot ⟨i.val, hi⟩

end JointFlagSample

/-- The first flag reads the ordered roots followed by the first free block. -/
def permutationLeftFlag {n roots free : Nat} (g : Graph (Fin n))
    (e : JointFlagPositions roots free ≃ Fin n) : Graph (Fin (roots + free)) :=
  comapBooleanGraph g (Fin.append (fun i => e (Sum.inl i))
    (fun i => e (Sum.inr (Sum.inl i))))

/-- The second flag reads the same ordered roots followed by the second free block. -/
def permutationRightFlag {n roots free : Nat} (g : Graph (Fin n))
    (e : JointFlagPositions roots free ≃ Fin n) : Graph (Fin (roots + free)) :=
  comapBooleanGraph g (Fin.append (fun i => e (Sum.inl i))
    (fun i => e (Sum.inr (Sum.inr i))))

noncomputable def permutationLeftFlagEquiv {n roots free : Nat}
    (g : Graph (Fin n)) (e : JointFlagPositions roots free ≃ Fin n) :
    RootedGraphEquiv roots (permutationLeftFlag g e)
      ((JointFlagSample.ofPermutation e).graph g) :=
  (JointFlagSample.ofPermutation e).orderedGraphEquiv
    ((JointFlagSample.ofPermutation e).compatibleLeftEquiv e
      (JointFlagSample.ofPermutation_compatible e)) g

noncomputable def permutationRightFlagEquiv {n roots free : Nat}
    (hn : n = roots + 2 * free) (g : Graph (Fin n))
    (e : JointFlagPositions roots free ≃ Fin n) :
    RootedGraphEquiv roots (permutationRightFlag g e)
      (((JointFlagSample.ofPermutation e).swap hn).graph g) :=
  ((JointFlagSample.ofPermutation e).swap hn).orderedGraphEquiv
    ((JointFlagSample.ofPermutation e).compatibleRightEquiv hn e
      (JointFlagSample.ofPermutation_compatible e)) g




theorem permutationLeftFlag_rootType {n roots free : Nat} (typeMask : Nat)
    (g : Graph (Fin n)) (e : JointFlagPositions roots free ≃ Fin n) :
    rootTypeCheck roots typeMask (permutationLeftFlag g e) = true ↔
      jointRootCheck (free := free) typeMask g (JointFlagSample.ofPermutation e).1 = true := by
  simp only [rootTypeCheck, jointRootCheck, decide_eq_true_eq]
  constructor
  · intro h i j
    simpa [permutationLeftFlag, comapBooleanGraph, Fin.append, JointFlagSample.ofPermutation] using
      h (i.castAdd free) (j.castAdd free) i.isLt j.isLt
  · intro h i j hi hj
    let a : Fin roots := ⟨i.val, hi⟩
    let b : Fin roots := ⟨j.val, hj⟩
    have ha : i = a.castAdd free := Fin.ext rfl
    have hb : j = b.castAdd free := Fin.ext rfl
    rw [ha, hb]
    simpa [permutationLeftFlag, comapBooleanGraph, Fin.append, JointFlagSample.ofPermutation] using h a b

/-- Root type and two rooted isomorphisms, stated using the permutation's own free orderings. -/
def PermutationBlockPairHasTypes {n roots free dimension : Nat}
    (typeMask : Nat) (basis : Vector Nat dimension) (g : Graph (Fin n))
    (i j : Fin dimension) (e : JointFlagPositions roots free ≃ Fin n) : Prop :=
  rootTypeCheck roots typeMask (permutationLeftFlag g e) = true ∧
    Nonempty (RootedGraphEquiv roots (permutationLeftFlag g e)
      (maskGraph (roots + free) basis[i])) ∧
    Nonempty (RootedGraphEquiv roots (permutationRightFlag g e)
      (maskGraph (roots + free) basis[j]))

theorem permutationBlockPairHasTypes_iff {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (g : Graph (Fin n)) (i j : Fin dimension) (e : JointFlagPositions roots free ≃ Fin n) :
    PermutationBlockPairHasTypes typeMask basis g i j e ↔
      JointFlagPairHasTypes hn typeMask basis g i j (JointFlagSample.ofPermutation e) := by
  unfold PermutationBlockPairHasTypes JointFlagPairHasTypes
  rw [permutationLeftFlag_rootType]
  have el := permutationLeftFlagEquiv g e
  have er := permutationRightFlagEquiv hn g e
  constructor
  · rintro ⟨hr, ⟨hl⟩, ⟨hh⟩⟩
    exact ⟨hr, ⟨el.symm.trans hl⟩, ⟨er.symm.trans hh⟩⟩
  · rintro ⟨hr, ⟨hl⟩, ⟨hh⟩⟩
    exact ⟨hr, ⟨el.trans hl⟩, ⟨er.trans hh⟩⟩





@[simp] theorem jointFlagPositionEquiv_root_val {n roots free : Nat}
    (hn : n = roots + 2 * free) (i : Fin roots) :
    (jointFlagPositionEquiv hn (Sum.inl i)).val = i.val := rfl

@[simp] theorem jointFlagPositionEquiv_left_val {n roots free : Nat}
    (hn : n = roots + 2 * free) (i : Fin free) :
    (jointFlagPositionEquiv hn (Sum.inr (Sum.inl i))).val = roots + i.val := rfl

@[simp] theorem jointFlagPositionEquiv_right_val {n roots free : Nat}
    (hn : n = roots + 2 * free) (i : Fin free) :
    (jointFlagPositionEquiv hn (Sum.inr (Sum.inr i))).val = roots + (free + i.val) := rfl

theorem fullPermutationBlockPair_probability {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (classify : Graph (Fin (roots + free)) → Fin dimension)
    (hclassify : ∀ g, rootTypeCheck roots typeMask g = true → ∀ i,
      classify g = i ↔ Nonempty (RootedGraphEquiv roots g
        (maskGraph (roots + free) basis[i])))
    (g : Graph (Fin n)) (i j : Fin dimension) :
    (Nat.card {p : Equiv.Perm (Fin n) //
      PermutationBlockPairHasTypes typeMask basis g i j (jointFlagFullPermutationEquiv hn p)} : ℚ) /
      n.factorial =
    (jointFlagPairCount hn (jointRootCheck (free := free) typeMask g)
      (fun x => classify (x.graph g)) i j : ℚ) /
        (n.descFactorial roots * (n - roots).choose free) := by
  let E : {p : Equiv.Perm (Fin n) //
      PermutationBlockPairHasTypes typeMask basis g i j (jointFlagFullPermutationEquiv hn p)} ≃
      {p : Equiv.Perm (Fin n) //
      JointFlagPairHasTypes hn typeMask basis g i j (jointFlagSampleOfPermutation hn p)} :=
    Equiv.subtypeEquivRight (fun p => permutationBlockPairHasTypes_iff hn typeMask basis g i j _)
  rw [Nat.card_congr E, jointFlagFullPermutation_probability,
    ← jointFlagPairCount_semantics hn typeMask basis classify hclassify g i j]

end InducedPentagons.Paper


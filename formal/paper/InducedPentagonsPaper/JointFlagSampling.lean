import InducedPentagonsPaper.SubsetGraphs
import Mathlib.Data.Fintype.CardEmbedding

/-! Ordered roots and disjoint unordered extension sets are the finite flag-product samples. -/

namespace InducedPentagons.Paper

def flagRootVertices {n roots : Nat} (f : Fin roots ↪ Fin n) : Finset (Fin n) :=
  Finset.univ.image f

theorem flagRootVertices_card {n roots : Nat} (f : Fin roots ↪ Fin n) :
    (flagRootVertices f).card = roots := by
  rw [flagRootVertices, Finset.card_image_of_injective _ f.injective]
  simp

def JointFlagSample (n roots free : Nat) :=
  Σ f : Fin roots ↪ Fin n,
    {s : Finset (Fin n) // s ⊆ (flagRootVertices f)ᶜ ∧ s.card = free}

noncomputable instance (n roots free : Nat) : Fintype (JointFlagSample n roots free) := by
  classical
  unfold JointFlagSample
  infer_instance

theorem jointFlag_left_choice_card {n roots free : Nat} (f : Fin roots ↪ Fin n) :
    Fintype.card {s : Finset (Fin n) // s ⊆ (flagRootVertices f)ᶜ ∧ s.card = free} =
      (n - roots).choose free := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun s : Finset (Fin n) =>
      s ⊆ (flagRootVertices f)ᶜ ∧ s.card = free)) = (flagRootVertices f)ᶜ.powersetCard free := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
  rw [he, Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin, flagRootVertices_card]

theorem jointFlagSample_card (n roots free : Nat) :
    Fintype.card (JointFlagSample n roots free) =
      n.descFactorial roots * (n - roots).choose free := by
  classical
  unfold JointFlagSample
  rw [Fintype.card_sigma]
  simp only [jointFlag_left_choice_card, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin]

theorem jointFlagSample_one_root_card : Fintype.card (JointFlagSample 7 1 3) = 140 := by
  rw [jointFlagSample_card]
  decide +kernel

theorem jointFlagSample_three_roots_card : Fintype.card (JointFlagSample 7 3 2) = 1260 := by
  rw [jointFlagSample_card]
  decide +kernel

namespace JointFlagSample

def left {n roots free : Nat} (x : JointFlagSample n roots free) : Finset (Fin n) := x.2.val

def right {n roots free : Nat} (x : JointFlagSample n roots free) : Finset (Fin n) :=
  (flagRootVertices x.1 ∪ x.left)ᶜ

theorem left_card {n roots free : Nat} (x : JointFlagSample n roots free) : x.left.card = free :=
  x.2.property.2

theorem roots_left_disjoint {n roots free : Nat} (x : JointFlagSample n roots free) :
    Disjoint (flagRootVertices x.1) x.left := by
  apply Finset.disjoint_left.mpr
  intro v hr hl
  exact (Finset.mem_compl.mp (x.2.property.1 hl)) hr

theorem right_available {n roots free : Nat} (x : JointFlagSample n roots free) :
    x.right ⊆ (flagRootVertices x.1)ᶜ := by
  intro v hv
  apply Finset.mem_compl.mpr
  intro hr
  exact (Finset.mem_compl.mp hv) (Finset.mem_union_left _ hr)

theorem right_card {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) : x.right.card = free := by
  rw [right, Finset.card_compl, Finset.card_union_of_disjoint x.roots_left_disjoint,
    flagRootVertices_card, x.left_card, Fintype.card_fin]
  omega

def swap {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) : JointFlagSample n roots free :=
  ⟨x.1, x.right, x.right_available, x.right_card hn⟩

theorem swap_right {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) : (swap hn x).right = x.left := by
  change (flagRootVertices x.1 ∪ (flagRootVertices x.1 ∪ x.left)ᶜ)ᶜ = x.left
  ext v
  simp only [Finset.mem_compl, Finset.mem_union]
  have hd : v ∈ x.left → v ∉ flagRootVertices x.1 :=
    fun hv => Finset.mem_compl.mp (x.2.property.1 hv)
  tauto

theorem swap_swap {n roots free : Nat} (hn : n = roots + 2 * free)
    (x : JointFlagSample n roots free) : swap hn (swap hn x) = x := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact swap_right hn x

def swapEquiv {n roots free : Nat} (hn : n = roots + 2 * free) :
    JointFlagSample n roots free ≃ JointFlagSample n roots free :=
  ⟨swap hn, swap hn, swap_swap hn, swap_swap hn⟩

end JointFlagSample

def jointFlagPairEquiv {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (valid : (Fin roots ↪ Fin n) → Bool) (classify : JointFlagSample n roots free → Fin dimension)
    (i j : Fin dimension) :
    {x : JointFlagSample n roots free // valid x.1 = true ∧ classify x = i ∧
      classify (x.swap hn) = j} ≃
    {x : JointFlagSample n roots free // valid x.1 = true ∧ classify x = j ∧
      classify (x.swap hn) = i} where
  toFun x := ⟨x.val.swap hn, x.property.1, x.property.2.2, by
    simpa only [JointFlagSample.swap_swap] using x.property.2.1⟩
  invFun x := ⟨x.val.swap hn, x.property.1, x.property.2.2, by
    simpa only [JointFlagSample.swap_swap] using x.property.2.1⟩
  left_inv x := Subtype.ext (JointFlagSample.swap_swap hn x.val)
  right_inv x := Subtype.ext (JointFlagSample.swap_swap hn x.val)

noncomputable def jointFlagPairCount {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (valid : (Fin roots ↪ Fin n) → Bool) (classify : JointFlagSample n roots free → Fin dimension)
    (i j : Fin dimension) : Nat := by
  classical
  exact Fintype.card {x : JointFlagSample n roots free // valid x.1 = true ∧
    classify x = i ∧ classify (x.swap hn) = j}

theorem jointFlagPairCount_symmetric {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (valid : (Fin roots ↪ Fin n) → Bool) (classify : JointFlagSample n roots free → Fin dimension)
    (i j : Fin dimension) :
    jointFlagPairCount hn valid classify i j = jointFlagPairCount hn valid classify j i := by
  classical
  exact Fintype.card_congr (jointFlagPairEquiv hn valid classify i j)

theorem jointFlagPairCount_le {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (valid : (Fin roots ↪ Fin n) → Bool) (classify : JointFlagSample n roots free → Fin dimension)
    (i j : Fin dimension) :
    jointFlagPairCount hn valid classify i j ≤ n.descFactorial roots * (n - roots).choose free := by
  classical
  rw [← jointFlagSample_card]
  exact Fintype.card_subtype_le _

end InducedPentagons.Paper

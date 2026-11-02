import InducedPentagonsPaper.JointFlagSampling
import InducedPentagonsPaper.Generated.IndexedFlagTables
import Mathlib.Data.Fin.Tuple.Basic

/-! The joint samples induce rooted flags on the actual host vertices. -/

namespace InducedPentagons.Paper

namespace JointFlagSample

def vertex {n roots free : Nat} (x : JointFlagSample n roots free) :
    Fin (roots + free) → Fin n :=
  Fin.append x.1 (subsetVertex x.left x.left_card)

@[simp] theorem vertex_root {n roots free : Nat} (x : JointFlagSample n roots free)
    (i : Fin roots) : x.vertex (i.castAdd free) = x.1 i := by
  simp [vertex, Fin.append]

@[simp] theorem vertex_free {n roots free : Nat} (x : JointFlagSample n roots free)
    (i : Fin free) : x.vertex (i.natAdd roots) = subsetVertex x.left x.left_card i := by
  simp [vertex, Fin.append]

theorem free_vertex_mem {n roots free : Nat} (x : JointFlagSample n roots free)
    (i : Fin free) : subsetVertex x.left x.left_card i ∈ x.left := by
  rw [subsetVertex_eq_orderEmb]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem vertex_injective {n roots free : Nat} (x : JointFlagSample n roots free) :
    Function.Injective x.vertex := by
  apply Fin.append_injective_iff.mpr
  refine ⟨x.1.injective, ?_, ?_⟩
  · rw [subsetVertex_eq_orderEmb]
    exact (x.left.orderEmbOfFin x.left_card).injective
  · intro i j he
    have hr : x.1 i ∈ flagRootVertices x.1 :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hl := x.free_vertex_mem j
    rw [← he] at hl
    exact (Finset.disjoint_left.mp x.roots_left_disjoint) hr hl

theorem vertex_mem {n roots free : Nat} (x : JointFlagSample n roots free)
    (i : Fin (roots + free)) : x.vertex i ∈ flagRootVertices x.1 ∪ x.left := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [vertex_root]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · rw [vertex_free]
    exact Finset.mem_union_right _ (x.free_vertex_mem j)

def graph {n roots free : Nat} (g : Graph (Fin n)) (x : JointFlagSample n roots free) :
    Graph (Fin (roots + free)) := comapBooleanGraph g x.vertex

end JointFlagSample

def jointRootCheck {n roots free : Nat} (typeMask : Nat) (g : Graph (Fin n))
    (f : Fin roots ↪ Fin n) : Bool :=
  decide (∀ i j : Fin roots, g.adj (f i) (f j) =
    (maskGraph (roots + free) typeMask).adj (i.castAdd free) (j.castAdd free))

theorem jointFlagGraph_rootType {n roots free : Nat} (typeMask : Nat)
    (g : Graph (Fin n)) (x : JointFlagSample n roots free) :
    rootTypeCheck roots typeMask (x.graph g) = true ↔
      jointRootCheck (free := free) typeMask g x.1 = true := by
  simp only [rootTypeCheck, jointRootCheck, decide_eq_true_eq]
  constructor
  · intro h i j
    simpa only [JointFlagSample.graph, comapBooleanGraph, JointFlagSample.vertex_root] using
      h (i.castAdd free) (j.castAdd free) i.isLt j.isLt
  · intro h i j hi hj
    let a : Fin roots := ⟨i.val, hi⟩
    let b : Fin roots := ⟨j.val, hj⟩
    have ha : i = a.castAdd free := Fin.ext rfl
    have hb : j = b.castAdd free := Fin.ext rfl
    rw [ha, hb]
    simpa only [JointFlagSample.graph, comapBooleanGraph, JointFlagSample.vertex_root] using h a b

theorem jointFlagGraph_swap_rootType {n roots free : Nat} (hn : n = roots + 2 * free)
    (typeMask : Nat) (g : Graph (Fin n)) (x : JointFlagSample n roots free) :
    rootTypeCheck roots typeMask ((x.swap hn).graph g) = true ↔
      rootTypeCheck roots typeMask (x.graph g) = true := by
  rw [jointFlagGraph_rootType, jointFlagGraph_rootType]
  rfl

def JointFlagPairHasTypes {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (typeMask : Nat) (basis : Vector Nat dimension) (g : Graph (Fin n))
    (i j : Fin dimension) (x : JointFlagSample n roots free) : Prop :=
  jointRootCheck (free := free) typeMask g x.1 = true ∧
    Nonempty (RootedGraphEquiv roots (x.graph g) (maskGraph (roots + free) basis[i])) ∧
    Nonempty (RootedGraphEquiv roots ((x.swap hn).graph g) (maskGraph (roots + free) basis[j]))

theorem jointFlagPair_classifier_iff {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (classify : Graph (Fin (roots + free)) → Fin dimension)
    (hclassify : ∀ g, rootTypeCheck roots typeMask g = true → ∀ i,
      classify g = i ↔ Nonempty (RootedGraphEquiv roots g
        (maskGraph (roots + free) basis[i])))
    (g : Graph (Fin n)) (i j : Fin dimension) (x : JointFlagSample n roots free) :
    (jointRootCheck (free := free) typeMask g x.1 = true ∧ classify (x.graph g) = i ∧
      classify ((x.swap hn).graph g) = j) ↔
      JointFlagPairHasTypes hn typeMask basis g i j x := by
  constructor
  · rintro ⟨hv, hi, hj⟩
    have hl := (jointFlagGraph_rootType typeMask g x).mpr hv
    have hr := (jointFlagGraph_swap_rootType hn typeMask g x).mpr hl
    exact ⟨hv, (hclassify _ hl i).mp hi, (hclassify _ hr j).mp hj⟩
  · rintro ⟨hv, hi, hj⟩
    have hl := (jointFlagGraph_rootType typeMask g x).mpr hv
    have hr := (jointFlagGraph_swap_rootType hn typeMask g x).mpr hl
    exact ⟨hv, (hclassify _ hl i).mpr hi, (hclassify _ hr j).mpr hj⟩

theorem jointFlagPairCount_semantics {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (classify : Graph (Fin (roots + free)) → Fin dimension)
    (hclassify : ∀ g, rootTypeCheck roots typeMask g = true → ∀ i,
      classify g = i ↔ Nonempty (RootedGraphEquiv roots g
        (maskGraph (roots + free) basis[i])))
    (g : Graph (Fin n)) (i j : Fin dimension) :
    jointFlagPairCount hn (jointRootCheck (free := free) typeMask g)
      (fun x => classify (x.graph g)) i j =
      Nat.card {x : JointFlagSample n roots free //
        JointFlagPairHasTypes hn typeMask basis g i j x} := by
  classical
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun x =>
    jointFlagPair_classifier_iff hn typeMask basis classify hclassify g i j x)

end InducedPentagons.Paper

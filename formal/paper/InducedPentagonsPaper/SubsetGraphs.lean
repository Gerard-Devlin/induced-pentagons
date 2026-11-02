import InducedPentagonsPaper.RootedClassification
import Mathlib.Data.Finset.Sort

/-! A sorted finite subset presents exactly the usual induced simple graph. -/

namespace InducedPentagons.Paper

def comapBooleanGraph {V W : Type} (g : Graph W) (f : V → W) : Graph V where
  adj i j := g.adj (f i) (f j)
  symmetric i j := g.symmetric (f i) (f j)
  loopless i := g.loopless (f i)

def kernelSort {n : Nat} (s : Finset (Fin n)) : List (Fin n) :=
  Quot.liftOn s.val (List.insertionSort (· ≤ ·)) (fun a b h =>
    ((List.perm_insertionSort (· ≤ ·) a).trans
      (h.trans (List.perm_insertionSort (· ≤ ·) b).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort (· ≤ ·) a) (List.pairwise_insertionSort (· ≤ ·) b))

theorem kernelSort_eq_sort {n : Nat} (s : Finset (Fin n)) : kernelSort s = s.sort := by
  unfold kernelSort Finset.sort Multiset.sort
  exact Quot.inductionOn s.val (fun l => (List.mergeSort_eq_insertionSort (· ≤ ·) l).symm)

def subsetVertex {n k : Nat} (s : Finset (Fin n)) (hs : s.card = k) (i : Fin k) : Fin n :=
  (kernelSort s)[i.val]'(by simpa only [kernelSort_eq_sort, Finset.length_sort, hs] using i.isLt)

theorem subsetVertex_eq_orderEmb {n k : Nat} (s : Finset (Fin n)) (hs : s.card = k) :
    subsetVertex s hs = s.orderEmbOfFin hs := by
  funext i
  rw [Finset.orderEmbOfFin_apply]
  simp only [subsetVertex, kernelSort_eq_sort, Fin.getElem_fin]

def subsetGraph {n k : Nat} (g : Graph (Fin n)) (s : Finset (Fin n))
    (hs : s.card = k) : Graph (Fin k) := comapBooleanGraph g (subsetVertex s hs)

def subsetGraphIso {n k : Nat} (g : Graph (Fin n)) (s : Finset (Fin n))
    (hs : s.card = k) :
    toSimpleGraph (subsetGraph g s hs) ≃g (toSimpleGraph g).induce (s : Set (Fin n)) where
  toEquiv := (s.orderIsoOfFin hs).toEquiv
  map_rel_iff' := by
    intro i j
    change g.adj (s.orderIsoOfFin hs i).val (s.orderIsoOfFin hs j).val = true ↔
      g.adj (subsetVertex s hs i) (subsetVertex s hs j) = true
    rw [Finset.coe_orderIsoOfFin_apply, Finset.coe_orderIsoOfFin_apply, subsetVertex_eq_orderEmb]

def InducedGraphTypeSet {n k : Nat} (h : Graph (Fin k)) (g : Graph (Fin n))
    (s : Finset (Fin n)) : Prop :=
  Nonempty (toSimpleGraph h ≃g (toSimpleGraph g).induce (s : Set (Fin n)))

theorem inducedGraphTypeSet_card {n k : Nat} {h : Graph (Fin k)} {g : Graph (Fin n)}
    {s : Finset (Fin n)} (hs : InducedGraphTypeSet h g s) : s.card = k := by
  obtain ⟨e⟩ := hs
  have he := Fintype.card_congr e.toEquiv
  simpa using he.symm

theorem inducedGraphTypeSet_iff_subsetGraphIso {n k : Nat} (h : Graph (Fin k))
    (g : Graph (Fin n)) (s : Finset (Fin n)) (hs : s.card = k) :
    InducedGraphTypeSet h g s ↔ Nonempty (toSimpleGraph (subsetGraph g s hs) ≃g toSimpleGraph h) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(subsetGraphIso g s hs).trans e.symm⟩
  · rintro ⟨e⟩
    exact ⟨e.symm.trans (subsetGraphIso g s hs)⟩

def complementEdgeCheck {n : Nat} (g : Graph (Fin n)) (s : Finset (Fin n)) : Bool :=
  (kernelSort sᶜ).any (fun u => (kernelSort sᶜ).any (fun v => g.adj u v))

theorem complementEdgeCheck_iff {n : Nat} (g : Graph (Fin n)) (s : Finset (Fin n)) :
    complementEdgeCheck g s = true ↔
      ∃ u v : Fin n, u ∉ s ∧ v ∉ s ∧ g.adj u v = true := by
  simp only [complementEdgeCheck, kernelSort_eq_sort, List.any_eq_true, Finset.mem_sort, Finset.mem_compl]
  aesop

theorem five_subset_complement_card {s : Finset (Fin 7)} (hs : s.card = 5) : sᶜ.card = 2 := by
  rw [Finset.card_compl, Fintype.card_fin, hs]

end InducedPentagons.Paper

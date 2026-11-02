import InducedPentagonsPaper.FiveVertexTypes
import InducedPentagonsPaper.SubsetGraphs

/-! The fixed-density columns count actual induced five-vertex subsets. -/

namespace InducedPentagons.Paper

def fixedSubsetCheck {n : Nat} (g : Graph (Fin n)) (m : Nat) (s : Finset (Fin n)) : Bool :=
  if hs : s.card = 5 then decide (fiveGraphType (subsetGraph g s hs) = m) else false

theorem fixedSubsetCheck_iff {n : Nat} (g : Graph (Fin n)) (m : Nat)
    (hm : m ∈ fixedTypeMasks) (s : Finset (Fin n)) :
    fixedSubsetCheck g m s = true ↔ InducedGraphTypeSet (maskGraph 5 m) g s := by
  unfold fixedSubsetCheck
  split_ifs with hs
  · rw [decide_eq_true_eq, fiveGraphType_eq_iff _ m hm]
    exact (inducedGraphTypeSet_iff_subsetGraphIso _ g s hs).symm
  · simp only [false_iff]
    intro h
    exact hs (inducedGraphTypeSet_card h)

def fixedComplementSubsetCheck {n : Nat} (g : Graph (Fin n)) (m : Nat)
    (s : Finset (Fin n)) : Bool := fixedSubsetCheck g m s && complementEdgeCheck g s

theorem fixedComplementSubsetCheck_iff {n : Nat} (g : Graph (Fin n)) (m : Nat)
    (hm : m ∈ fixedTypeMasks) (s : Finset (Fin n)) :
    fixedComplementSubsetCheck g m s = true ↔
      InducedGraphTypeSet (maskGraph 5 m) g s ∧
        ∃ u v : Fin n, u ∉ s ∧ v ∉ s ∧ g.adj u v = true := by
  rw [fixedComplementSubsetCheck, Bool.and_eq_true_iff,
    fixedSubsetCheck_iff g m hm, complementEdgeCheck_iff]

def fixedDensityCount {n : Nat} (g : Graph (Fin n)) (m : Nat) : Nat :=
  ((Finset.univ.powersetCard 5).filter (fun s => fixedSubsetCheck g m s)).card

def fixedComplementCount {n : Nat} (g : Graph (Fin n)) (m : Nat) : Nat :=
  ((Finset.univ.powersetCard 5).filter (fun s => fixedComplementSubsetCheck g m s)).card

noncomputable def inducedTypeSetCount {n k : Nat} (h : Graph (Fin k)) (g : Graph (Fin n)) : Nat := by
  classical
  exact Fintype.card {s : Finset (Fin n) // InducedGraphTypeSet h g s}

noncomputable def inducedTypeComplementCount {n k : Nat} (h : Graph (Fin k))
    (g : Graph (Fin n)) : Nat := by
  classical
  exact Fintype.card {s : Finset (Fin n) // InducedGraphTypeSet h g s ∧
    ∃ u v : Fin n, u ∉ s ∧ v ∉ s ∧ g.adj u v = true}

theorem fixedDensityCount_semantics {n : Nat} (g : Graph (Fin n)) (m : Nat)
    (hm : m ∈ fixedTypeMasks) :
    fixedDensityCount g m = inducedTypeSetCount (maskGraph 5 m) g := by
  classical
  unfold fixedDensityCount inducedTypeSetCount
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext s
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    Finset.mem_univ, fixedSubsetCheck_iff g m hm]
  exact ⟨fun h => h.2, fun h => ⟨inducedGraphTypeSet_card h, h⟩⟩

theorem fixedComplementCount_semantics {n : Nat} (g : Graph (Fin n)) (m : Nat)
    (hm : m ∈ fixedTypeMasks) :
    fixedComplementCount g m = inducedTypeComplementCount (maskGraph 5 m) g := by
  classical
  unfold fixedComplementCount inducedTypeComplementCount
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext s
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    Finset.mem_univ, fixedComplementSubsetCheck_iff g m hm]
  exact ⟨fun h => h.2, fun h => ⟨inducedGraphTypeSet_card h.1, h⟩⟩

def fixedDensityCounts {n : Nat} (g : Graph (Fin n)) : List Nat :=
  fixedTypeMasks.map (fixedDensityCount g)

def fixedComplementCounts {n : Nat} (g : Graph (Fin n)) : List Nat :=
  fixedTypeMasks.map (fixedComplementCount g)

theorem fixedDensityCounts_semantics {n : Nat} (g : Graph (Fin n)) :
    fixedDensityCounts g = fixedTypeMasks.map (fun m => inducedTypeSetCount (maskGraph 5 m) g) := by
  apply List.map_congr_left
  intro m hm
  exact fixedDensityCount_semantics g m hm

theorem fixedComplementCounts_semantics {n : Nat} (g : Graph (Fin n)) :
    fixedComplementCounts g =
      fixedTypeMasks.map (fun m => inducedTypeComplementCount (maskGraph 5 m) g) := by
  apply List.map_congr_left
  intro m hm
  exact fixedComplementCount_semantics g m hm

theorem fixedDensityCount_le {n : Nat} (g : Graph (Fin n)) (m : Nat) :
    fixedDensityCount g m ≤ n.choose 5 := by
  simpa [fixedDensityCount, Finset.card_powersetCard] using
    (Finset.card_filter_le (s := Finset.univ.powersetCard 5) (fun s => fixedSubsetCheck g m s))

theorem fixedComplementCount_le {n : Nat} (g : Graph (Fin n)) (m : Nat) :
    fixedComplementCount g m ≤ fixedDensityCount g m := by
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter, fixedComplementSubsetCheck, Bool.and_eq_true_iff] at hs ⊢
  exact ⟨hs.1, hs.2.1⟩

theorem five_subsets_of_seven_count :
    (Finset.univ.powersetCard 5 : Finset (Finset (Fin 7))).card = 21 := by
  norm_num [Finset.card_powersetCard, Nat.choose]

end InducedPentagons.Paper

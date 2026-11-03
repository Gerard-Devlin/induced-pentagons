import InducedPentagonsPaper.GraphEncoding
import InducedPentagonsPaper.PatternSteps

/-! Automorphism census by complete, duplicate-free induced-pattern enumeration. -/

namespace InducedPentagons.Paper

/-- A complete graph pattern, retaining one orientation of each distinct pair. -/
def censusPattern {n : Nat} (g : Graph (Fin n)) : PartialPattern n where
  edges := (upperPairs n).filter (fun e => g.adj e.1 e.2)
  nonedges := (upperPairs n).filter (fun e => !(g.adj e.1 e.2))

theorem censusPattern_ordered {n : Nat} (g : Graph (Fin n)) :
    OrderedPattern (censusPattern g) := by
  constructor <;> intro e he
  all_goals exact (mem_upperPairs e).mp (List.mem_filter.mp he).1

theorem censusPattern_satisfies_iff {n : Nat} (g h : Graph (Fin n))
    (f : Fin n → Fin n) :
    PatternSatisfies (censusPattern g) h f ↔
      ∀ i j, h.adj (f i) (f j) = g.adj i j := by
  constructor
  · intro hp
    have forward (i j : Fin n) (hij : i.val < j.val) :
        h.adj (f i) (f j) = g.adj i j := by
      cases hg : g.adj i j with
      | false =>
        exact hp.2 (i, j) (List.mem_filter.mpr
          ⟨(mem_upperPairs _).mpr hij, by simp [hg]⟩)
      | true =>
        exact hp.1 (i, j) (List.mem_filter.mpr ⟨(mem_upperPairs _).mpr hij, hg⟩)
    intro i j
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact forward i j hij
    · have he : i = j := Fin.ext hij
      subst j
      simp [Graph.loopless]
    · rw [h.symmetric, g.symmetric]
      exact forward j i hij
  · intro hp
    constructor
    · intro e he
      exact (hp e.1 e.2).trans (List.mem_filter.mp he).2
    · intro e he
      have hn := (List.mem_filter.mp he).2
      have hg : g.adj e.1 e.2 = false := by simpa using hn
      exact (hp e.1 e.2).trans hg

/-- The finite injections being counted are exactly the ordinary graph isomorphisms. -/
noncomputable def censusPatternIsoEquiv {n : Nat} (g h : Graph (Fin n)) :
    PatternInjection (censusPattern g) h ≃ (toSimpleGraph g ≃g toSimpleGraph h) where
  toFun f := (BooleanGraphEquiv.toSimpleGraphIso
    ⟨Equiv.ofBijective f.val ⟨f.property.1, Finite.surjective_of_injective f.property.1⟩,
      (censusPattern_satisfies_iff g h f.val).mp f.property.2⟩)
  invFun e := ⟨e, e.injective, (censusPattern_satisfies_iff g h e).mpr
    (fun _ _ => Bool.eq_iff_iff.mpr e.map_rel_iff)⟩
  left_inv f := rfl
  right_inv e := by ext i; rfl

/-- Executable automorphism count with adjacency constraints checked as vertices are added. -/
def censusAutomorphismCount {n : Nat} (g : Graph (Fin n)) : Nat :=
  (fastPatternEnumeration (censusPattern g) g).length

theorem censusAutomorphismCount_semantics {n : Nat} (g : Graph (Fin n)) :
    censusAutomorphismCount g = Nat.card (toSimpleGraph g ≃g toSimpleGraph g) := by
  rw [censusAutomorphismCount, ← fastPatternEnumeration_count (censusPattern_ordered g)]
  rw [patternInjectionCount, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (censusPatternIsoEquiv g g)

theorem censusAutomorphismCount_pos {n : Nat} (g : Graph (Fin n)) :
    0 < censusAutomorphismCount g := by
  rw [censusAutomorphismCount, ← fastPatternEnumeration_count (censusPattern_ordered g)]
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨id, Function.injective_id,
    (censusPattern_satisfies_iff g g id).mpr (fun _ _ => rfl)⟩⟩

end InducedPentagons.Paper


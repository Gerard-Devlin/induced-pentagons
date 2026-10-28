import InducedPentagonsPaper.FiniteGraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-! A pruned, complete independent-set enumeration. Only independent partial
sets are extended; the Clebsch independence bound is checked on that family. -/

namespace InducedPentagons.Paper

def Independent {V : Type} (g : Graph V) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → g.adj u v = false

def independentSubsetsFrom {V : Type} (g : Graph V) : List V → List (List V)
  | [] => [[]]
  | v :: rest =>
      let family := independentSubsetsFrom g rest
      family ++ (family.filter (fun s => s.all (fun w => !(g.adj v w)))).map (v :: ·)

theorem independentSubsetsFrom_complete {V : Type} [DecidableEq V]
    (g : Graph V) (l : List V) (s : Finset V)
    (hcover : ∀ v ∈ s, v ∈ l) (hi : Independent g s) :
    ∃ t ∈ independentSubsetsFrom g l, t.toFinset = s := by
  induction l generalizing s with
  | nil =>
    have he : s = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      simpa using hcover v hv
    subst s
    exact ⟨[], by simp [independentSubsetsFrom], by simp⟩
  | cons v rest ih =>
    by_cases hv : v ∈ s
    · have hc : ∀ w ∈ s.erase v, w ∈ rest := by
        intro w hw
        rcases List.mem_cons.mp (hcover w (Finset.mem_of_mem_erase hw)) with he | hr
        · exact False.elim ((Finset.ne_of_mem_erase hw) he)
        · exact hr
      have hi' : Independent g (s.erase v) := by
        intro a ha b hb hab
        exact hi a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
      obtain ⟨t, ht, he⟩ := ih (s.erase v) hc hi'
      have hall : t.all (fun w => !(g.adj v w)) = true := by
        apply List.all_eq_true.mpr
        intro w hw
        have hw' : w ∈ s.erase v := by rw [← he]; exact List.mem_toFinset.mpr hw
        have hg := hi v hv w (Finset.mem_of_mem_erase hw') (Finset.ne_of_mem_erase hw').symm
        simp [hg]
      refine ⟨v :: t, ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨t, List.mem_filter.mpr ⟨ht, hall⟩, rfl⟩))
      · simp [he, Finset.insert_erase hv]
    · have hc : ∀ w ∈ s, w ∈ rest := by
        intro w hw
        rcases List.mem_cons.mp (hcover w hw) with he | hr
        · exact False.elim (hv (he ▸ hw))
        · exact hr
      obtain ⟨t, ht, he⟩ := ih s hc hi
      exact ⟨t, List.mem_append.mpr (Or.inl ht), he⟩

set_option maxRecDepth 10000 in
theorem clebsch_independent_family_bound :
    (independentSubsetsFrom clebsch (List.finRange 16)).all
      (fun t => decide (t.length ≤ 5)) = true := by decide +kernel

theorem clebsch_independent_card_le {s : Finset (Fin 16)} (hi : Independent clebsch s) :
    s.card ≤ 5 := by
  obtain ⟨t, ht, he⟩ := independentSubsetsFrom_complete clebsch (List.finRange 16) s
    (by simp) hi
  have hb := of_decide_eq_true (List.all_eq_true.mp clebsch_independent_family_bound t ht)
  rw [← he]
  exact (List.toFinset_card_le t).trans hb

theorem clebsch_complement_cliqueFree : (toSimpleGraph clebsch)ᶜ.CliqueFree 6 := by
  intro s hs
  have hi : Independent clebsch s := by
    intro u hu v hv huv
    have h := (SimpleGraph.compl_adj _ u v).mp (hs.isClique hu hv huv)
    exact Bool.eq_false_iff.mpr h.2
  have hb := clebsch_independent_card_le hi
  have hc := hs.card_eq
  omega

end InducedPentagons.Paper

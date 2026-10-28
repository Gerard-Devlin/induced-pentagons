import InducedPentagonsPaper.WeightedGraph
import Mathlib.Data.List.Nodup

/-! A complete, duplicate-free enumeration of labelled pentagon embeddings.
The enumeration follows four graph edges and then checks the full induced
pattern. It avoids enumerating all n^5 vertex maps. -/

namespace InducedPentagons.Paper

def tupleOfMap {n : Nat} (p : Fin 5 → Fin n) : PentagonTuple n :=
  ⟨p 0, p 1, p 2, p 3, p 4⟩

@[simp] theorem tupleOfMap_vertex {n : Nat} (p : Fin 5 → Fin n) :
    (tupleOfMap p).vertex = p := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem tupleOfMap_vertex_inverse {n : Nat} (p : PentagonTuple n) :
    tupleOfMap p.vertex = p := by cases p; rfl

def labelledPentagons {n : Nat} (g : Graph (Fin n)) : List (PentagonTuple n) :=
  (candidateWalks g).filter (fun p => decide (IsInducedPentagon g p.vertex))

theorem mem_labelledPentagons {n : Nat} (g : Graph (Fin n)) (p : PentagonTuple n) :
    p ∈ labelledPentagons g ↔ IsInducedPentagon g p.vertex := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    have hab : g.adj p.a p.b = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using h ⟨0, by decide⟩ ⟨1, by decide⟩
    have hbc : g.adj p.b p.c = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using h ⟨1, by decide⟩ ⟨2, by decide⟩
    have hcd : g.adj p.c p.d = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using h ⟨2, by decide⟩ ⟨3, by decide⟩
    have hde : g.adj p.d p.e = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using h ⟨3, by decide⟩ ⟨4, by decide⟩
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa using h⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.a, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.b, (mem_neighbors g p.a p.b).mpr hab, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.c, (mem_neighbors g p.b p.c).mpr hbc, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.d, (mem_neighbors g p.c p.d).mpr hcd, ?_⟩
    exact List.mem_map.mpr ⟨p.e, (mem_neighbors g p.d p.e).mpr hde, rfl⟩

theorem nodup_tagged_flatMap {α β : Type*} (l : List α) (f : α → List β)
    (key : β → α) (hl : l.Nodup) (hf : ∀ a, (f a).Nodup)
    (hk : ∀ a p, p ∈ f a → key p = a) : (l.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun a _ => hf a, hl.imp ?_⟩
  intro a b hab p hp hp'
  exact hab ((hk a p hp).symm.trans (hk b p hp'))

theorem candidateWalks_nodup {n : Nat} (g : Graph (Fin n)) :
    (candidateWalks g).Nodup := by
  have hn : ∀ u, (neighbors g u).Nodup :=
    fun u => (List.nodup_finRange n).filter _
  unfold candidateWalks
  apply nodup_tagged_flatMap _ _ (fun p => p.a) (List.nodup_finRange n)
  · intro a
    apply nodup_tagged_flatMap _ _ (fun p => p.b) (hn a)
    · intro b
      apply nodup_tagged_flatMap _ _ (fun p => p.c) (hn b)
      · intro c
        apply nodup_tagged_flatMap _ _ (fun p => p.d) (hn c)
        · intro d
          exact (hn d).map (fun e f h => by injection h)
        · intro d p hp
          rcases List.mem_map.mp hp with ⟨e, _, rfl⟩
          rfl
      · intro c p hp
        simp only [List.mem_flatMap, List.mem_map] at hp
        rcases hp with ⟨d, _, e, _, rfl⟩
        rfl
    · intro b p hp
      simp only [List.mem_flatMap, List.mem_map] at hp
      rcases hp with ⟨c, _, d, _, e, _, rfl⟩
      rfl
  · intro a p hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    rcases hp with ⟨b, _, c, _, d, _, e, _, rfl⟩
    rfl

theorem labelledPentagons_nodup {n : Nat} (g : Graph (Fin n)) :
    (labelledPentagons g).Nodup := (candidateWalks_nodup g).filter _

def labelledPentagonEquiv {n : Nat} (g : Graph (Fin n)) :
    PentagonEmbedding g ≃ ↥(labelledPentagons g).toFinset where
  toFun p := ⟨tupleOfMap p.val, by
    apply List.mem_toFinset.mpr
    apply (mem_labelledPentagons g _).mpr
    rw [tupleOfMap_vertex]
    exact p.property⟩
  invFun p := ⟨p.val.vertex, (mem_labelledPentagons g _).mp
    (List.mem_toFinset.mp p.property)⟩
  left_inv p := Subtype.ext (tupleOfMap_vertex p.val)
  right_inv p := Subtype.ext (tupleOfMap_vertex_inverse p.val)

theorem pentagon_card_eq_labelled_length {n : Nat} (g : Graph (Fin n)) :
    Fintype.card (PentagonEmbedding g) = (labelledPentagons g).length := by
  rw [Fintype.card_congr (labelledPentagonEquiv g), Fintype.card_coe]
  exact List.toFinset_card_of_nodup (labelledPentagons_nodup g)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clebsch_labelled_pentagons : (labelledPentagons clebsch).length = 1920 := by
  decide +kernel

theorem clebsch_pentagon_card : Fintype.card (PentagonEmbedding clebsch) = 1920 := by
  rw [pentagon_card_eq_labelled_length, clebsch_labelled_pentagons]

theorem clebsch_pentagonMass_unit : pentagonMass clebsch (fun _ => 1) = 192 := by
  rw [pentagonMass_unit, clebsch_pentagon_card]
  norm_num

theorem clebsch_balanced_pentagonMass (k : ℝ) :
    pentagonMass clebsch (fun _ => k) = 192 * k ^ 5 := by
  simpa [clebsch_pentagonMass_unit, mul_comm] using
    pentagonMass_scale clebsch (fun _ => 1) k

theorem clebsch_blowUp_pentagons {W : Type} [Fintype W] :
    pentagonMass (blowUp clebsch W) (fun _ => 1) = 192 * (Fintype.card W : ℝ) ^ 5 := by
  rw [pentagonMass_blowUp]
  have h : classMass (fun _ : Fin 16 × W => (1 : ℝ)) =
      fun _ => (Fintype.card W : ℝ) := by
    funext v
    simp [classMass]
  rw [h, clebsch_balanced_pentagonMass]

end InducedPentagons.Paper

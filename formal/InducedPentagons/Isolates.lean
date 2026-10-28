import InducedPentagons.FiniteGraph

namespace InducedPentagons

def withIsolates {V : Type} (g : Graph V) (W : Type) : Graph (Sum V W) where
  adj u v := match u, v with
    | .inl a, .inl b => g.adj a b
    | _, _ => false
  symmetric u v := by
    cases u <;> cases v <;> simp only
    · exact g.symmetric _ _
    all_goals rfl
  loopless u := by
    cases u
    · exact g.loopless _
    · rfl

theorem cycle_has_neighbor : ∀ i : Fin 5, ∃ j : Fin 5, cycleAdj i j = true := by
  decide +kernel

theorem pentagon_avoids_isolates {V W : Type} {g : Graph V}
    {p : Fin 5 → Sum V W} (h : IsInducedPentagon (withIsolates g W) p) :
    ∀ i, ∃ v, p i = Sum.inl v := by
  intro i
  cases hi : p i with
  | inl v => exact ⟨v, rfl⟩
  | inr w =>
    obtain ⟨j, hj⟩ := cycle_has_neighbor i
    have edge := h i j
    simp [withIsolates, hi, hj] at edge

def removeIsolatesVertex {V W : Type} {g : Graph V} {p : Fin 5 → Sum V W}
    (h : IsInducedPentagon (withIsolates g W) p) (i : Fin 5) : V :=
  match hi : p i with
  | .inl v => v
  | .inr _ => False.elim (by
      obtain ⟨v, hv⟩ := pentagon_avoids_isolates h i
      simp [hi] at hv)

theorem removeIsolatesVertex_spec {V W : Type} {g : Graph V}
    {p : Fin 5 → Sum V W} (h : IsInducedPentagon (withIsolates g W) p) (i : Fin 5) :
    p i = Sum.inl (removeIsolatesVertex h i) := by
  unfold removeIsolatesVertex
  split
  next v hv => exact hv
  next w hw =>
    obtain ⟨v, hv⟩ := pentagon_avoids_isolates h i
    simp [hw] at hv

def addIsolatesPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding g) : PentagonEmbedding (withIsolates g W) :=
  ⟨fun i => Sum.inl (p.val i), p.property⟩

def removeIsolatesPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding (withIsolates g W)) : PentagonEmbedding g :=
  ⟨removeIsolatesVertex p.property, by
    intro i j
    have h := p.property i j
    rw [removeIsolatesVertex_spec p.property i, removeIsolatesVertex_spec p.property j] at h
    exact h⟩

theorem remove_addIsolatesPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding g) :
    removeIsolatesPentagon (addIsolatesPentagon (W := W) p) = p := by
  apply Subtype.ext
  funext i
  exact (Sum.inl.inj (removeIsolatesVertex_spec
    (addIsolatesPentagon (W := W) p).property i)).symm

theorem add_removeIsolatesPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding (withIsolates g W)) :
    addIsolatesPentagon (removeIsolatesPentagon p) = p := by
  apply Subtype.ext
  funext i
  exact (removeIsolatesVertex_spec p.property i).symm

end InducedPentagons

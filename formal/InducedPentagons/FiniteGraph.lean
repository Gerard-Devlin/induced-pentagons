import Std

/-! Finite graph semantics independent of the imported certificate tensors. -/

namespace InducedPentagons

structure Graph (V : Type) where
  adj : V → V → Bool
  symmetric : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def cycleAdj (i j : Fin 5) : Bool :=
  (i.val + 1) % 5 == j.val || (j.val + 1) % 5 == i.val

def IsInducedPentagon {V : Type} (g : Graph V) (p : Fin 5 → V) : Prop :=
  ∀ i j, g.adj (p i) (p j) = cycleAdj i j

theorem cycle_has_no_twins : ∀ i j : Fin 5,
    (∀ k : Fin 5, cycleAdj i k = cycleAdj j k) → i = j := by decide +kernel

theorem inducedPentagon_injective {V : Type} {g : Graph V} {p : Fin 5 → V}
    (h : IsInducedPentagon g p) : Function.Injective p := by
  intro i j hij
  apply cycle_has_no_twins i j
  intro k
  rw [← h i k, ← h j k, hij]

def blowUp {V : Type} (g : Graph V) (W : Type) : Graph (V × W) where
  adj u v := g.adj u.1 v.1
  symmetric u v := g.symmetric u.1 v.1
  loopless u := g.loopless u.1

theorem blowUp_projection_induced {V W : Type} {g : Graph V}
    {p : Fin 5 → V × W} (h : IsInducedPentagon (blowUp g W) p) :
    IsInducedPentagon g (fun i => (p i).1) := h

theorem blowUp_projection_injective {V W : Type} {g : Graph V}
    {p : Fin 5 → V × W} (h : IsInducedPentagon (blowUp g W) p) :
    Function.Injective (fun i => (p i).1) :=
  inducedPentagon_injective (blowUp_projection_induced h)

def PentagonEmbedding {V : Type} (g : Graph V) :=
  { p : Fin 5 → V // IsInducedPentagon g p }

def liftPentagon {V W : Type} {g : Graph V} (p : PentagonEmbedding g)
    (clones : Fin 5 → W) : PentagonEmbedding (blowUp g W) :=
  ⟨fun i => (p.val i, clones i), p.property⟩

def projectPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding (blowUp g W)) : PentagonEmbedding g :=
  ⟨fun i => (p.val i).1, blowUp_projection_induced p.property⟩

theorem project_liftPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding g) (clones : Fin 5 → W) :
    projectPentagon (liftPentagon p clones) = p := by
  apply Subtype.ext
  rfl

theorem lift_projectPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding (blowUp g W)) :
    liftPentagon (projectPentagon p) (fun i => (p.val i).2) = p := by
  apply Subtype.ext
  rfl

theorem clone_liftPentagon {V W : Type} {g : Graph V}
    (p : PentagonEmbedding g) (clones : Fin 5 → W) :
    (fun i => ((liftPentagon p clones).val i).2) = clones := rfl

def neighbors {n : Nat} (g : Graph (Fin n)) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter (g.adj u)

theorem mem_neighbors {n : Nat} (g : Graph (Fin n)) (u v : Fin n) :
    v ∈ neighbors g u ↔ g.adj u v = true := by
  simp [neighbors]

def edgeCount {n : Nat} (g : Graph (Fin n)) : Nat :=
  (List.finRange n).foldl (fun total u => total +
    ((neighbors g u).filter (fun v => u.val < v.val)).length) 0

structure PentagonTuple (n : Nat) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  e : Fin n
  deriving Repr, BEq, DecidableEq

def PentagonTuple.vertex {n : Nat} (p : PentagonTuple n) (i : Fin 5) : Fin n :=
  match i.val with
  | 0 => p.a
  | 1 => p.b
  | 2 => p.c
  | 3 => p.d
  | _ => p.e

def canonicalTuple {n : Nat} (p : PentagonTuple n) : Bool :=
  p.a.val < p.b.val && p.a.val < p.c.val && p.a.val < p.d.val &&
  p.a.val < p.e.val && p.b.val < p.e.val

instance {n : Nat} (g : Graph (Fin n)) (p : PentagonTuple n) :
    Decidable (IsInducedPentagon g p.vertex) := inferInstanceAs
      (Decidable (∀ i j : Fin 5, g.adj (p.vertex i) (p.vertex j) = cycleAdj i j))

def normalizedPentagon {n : Nat} (g : Graph (Fin n)) (p : PentagonTuple n) : Bool :=
  canonicalTuple p && decide (IsInducedPentagon g p.vertex)

def candidateWalks {n : Nat} (g : Graph (Fin n)) : List (PentagonTuple n) :=
  (List.finRange n).flatMap fun a =>
    (neighbors g a).flatMap fun b =>
      (neighbors g b).flatMap fun c =>
        (neighbors g c).flatMap fun d =>
          (neighbors g d).map fun e => ⟨a, b, c, d, e⟩

def inducedPentagons {n : Nat} (g : Graph (Fin n)) : List (PentagonTuple n) :=
  (candidateWalks g).filter (normalizedPentagon g)

/-- The enumeration contains precisely the normalized induced embeddings. -/
theorem mem_inducedPentagons {n : Nat} (g : Graph (Fin n)) (p : PentagonTuple n) :
    p ∈ inducedPentagons g ↔ normalizedPentagon g p = true := by
  constructor
  · intro h
    exact (List.mem_filter.mp h).2
  · intro h
    have hi : IsInducedPentagon g p.vertex :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    have hab : g.adj p.a p.b = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using hi ⟨0, by decide⟩ ⟨1, by decide⟩
    have hbc : g.adj p.b p.c = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using hi ⟨1, by decide⟩ ⟨2, by decide⟩
    have hcd : g.adj p.c p.d = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using hi ⟨2, by decide⟩ ⟨3, by decide⟩
    have hde : g.adj p.d p.e = true := by
      simpa [PentagonTuple.vertex, cycleAdj] using hi ⟨3, by decide⟩ ⟨4, by decide⟩
    apply List.mem_filter.mpr
    refine ⟨?_, h⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.a, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.b, (mem_neighbors g p.a p.b).mpr hab, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.c, (mem_neighbors g p.b p.c).mpr hbc, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.d, (mem_neighbors g p.c p.d).mpr hcd, ?_⟩
    apply List.mem_map.mpr
    exact ⟨p.e, (mem_neighbors g p.d p.e).mpr hde, rfl⟩

def clebschAdj (u v : Fin 16) : Bool :=
  ([1, 2, 4, 8, 15] : List Nat).contains (u.val ^^^ v.val)

def clebsch : Graph (Fin 16) where
  adj := clebschAdj
  symmetric := by decide +kernel
  loopless := by decide +kernel

theorem clebsch_degree : ∀ v : Fin 16, (neighbors clebsch v).length = 5 := by
  decide +kernel

theorem clebsch_edges : edgeCount clebsch = 40 := by decide +kernel

theorem clebsch_triangle_free : ∀ u v w : Fin 16,
    clebsch.adj u v = true → clebsch.adj v w = true → clebsch.adj u w = false := by
  decide +kernel

theorem clebsch_codegrees : ∀ u v : Fin 16, u ≠ v →
    ((neighbors clebsch u).filter (clebsch.adj v)).length =
      (if clebsch.adj u v then 0 else 2) := by decide +kernel

end InducedPentagons

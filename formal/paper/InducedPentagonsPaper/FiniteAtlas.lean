import InducedPentagonsPaper.FiniteGraph
import Mathlib.Tactic

/-! Sound finite graph-atlas coverage by checked one-vertex extensions. -/

namespace InducedPentagons.Paper

def BooleanGraphEquiv {V W : Type} (g : Graph V) (h : Graph W) :=
  {e : V ≃ W // ∀ u v, h.adj (e u) (e v) = g.adj u v}

def BooleanGraphEquiv.trans {U V W : Type} {g : Graph U} {h : Graph V} {k : Graph W}
    (e : BooleanGraphEquiv g h) (f : BooleanGraphEquiv h k) : BooleanGraphEquiv g k :=
  ⟨e.val.trans f.val, fun u v => (f.property (e.val u) (e.val v)).trans (e.property u v)⟩

def BooleanGraphEquiv.toSimpleGraphIso {V W : Type} {g : Graph V} {h : Graph W}
    (e : BooleanGraphEquiv g h) : toSimpleGraph g ≃g toSimpleGraph h where
  toEquiv := e.val
  map_rel_iff' := by
    intro u v
    change h.adj (e.val u) (e.val v) = true ↔ g.adj u v = true
    rw [e.property]

def atlasEdgeIndex (n i j : Nat) : Nat := i * (2 * n - i - 1) / 2 + (j - i - 1)

def maskGraph (n mask : Nat) : Graph (Fin n) where
  adj u v := decide (u.val ≠ v.val) &&
    mask.testBit (atlasEdgeIndex n (min u.val v.val) (max u.val v.val))
  symmetric u v := by simp only [ne_comm, min_comm, max_comm]
  loopless u := by simp

def restrictLastGraph {n : Nat} (g : Graph (Fin (n + 1))) : Graph (Fin n) where
  adj u v := g.adj u.castSucc v.castSucc
  symmetric u v := g.symmetric u.castSucc v.castSucc
  loopless u := g.loopless u.castSucc

def extendGraph {n : Nat} (g : Graph (Fin n)) (b : Fin n → Bool) : Graph (Fin (n + 1)) where
  adj := Fin.lastCases (Fin.lastCases false b)
    (fun i => Fin.lastCases (b i) (fun j => g.adj i j))
  symmetric := by
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [g.symmetric]
  loopless := by
    intro i
    induction i using Fin.lastCases <;> simp [g.loopless]

def extendLastEquiv {n : Nat} (e : Fin n ≃ Fin n) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.lastCases (Fin.last n) (fun i => (e i).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun i => (e.symm i).castSucc)
  left_inv i := by induction i using Fin.lastCases <;> simp
  right_inv i := by induction i using Fin.lastCases <;> simp

def extensionNeighborhood {n : Nat} (g : Graph (Fin (n + 1)))
    (e : Fin n ≃ Fin n) (i : Fin n) : Bool := g.adj (e.symm i).castSucc (Fin.last n)

def graphExtensionEquiv {n : Nat} {g : Graph (Fin (n + 1))} {h : Graph (Fin n)}
    (e : BooleanGraphEquiv (restrictLastGraph g) h) :
    BooleanGraphEquiv g (extendGraph h (extensionNeighborhood g e.val)) := by
  refine ⟨extendLastEquiv e.val, ?_⟩
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp [extendLastEquiv, extendGraph, g.loopless]
  · simp [extendLastEquiv, extendGraph, extensionNeighborhood, g.symmetric]
  · simp [extendLastEquiv, extendGraph, extensionNeighborhood]
  · simpa [extendLastEquiv, extendGraph, restrictLastGraph] using e.property _ _

def AtlasCovers (n : Nat) (masks : List Nat) : Prop :=
  ∀ g : Graph (Fin n), ∃ m ∈ masks, Nonempty (BooleanGraphEquiv g (maskGraph n m))

def AtlasExtends (n : Nat) (previous next : List Nat) : Prop :=
  ∀ m ∈ previous, ∀ b : Fin n → Bool,
    ∃ k ∈ next, Nonempty (BooleanGraphEquiv (extendGraph (maskGraph n m) b) (maskGraph (n + 1) k))

theorem atlasCovers_zero : AtlasCovers 0 [0] := by
  intro g
  refine ⟨0, by simp, ⟨⟨Equiv.refl _, ?_⟩⟩⟩
  intro i
  exact Fin.elim0 i

theorem atlasCovers_succ {n : Nat} {previous next : List Nat}
    (hp : AtlasCovers n previous) (hs : AtlasExtends n previous next) :
    AtlasCovers (n + 1) next := by
  intro g
  obtain ⟨m, hm, ⟨e⟩⟩ := hp (restrictLastGraph g)
  obtain ⟨k, hk, ⟨f⟩⟩ := hs m hm (extensionNeighborhood g e.val)
  exact ⟨k, hk, ⟨(graphExtensionEquiv e).trans f⟩⟩

def maskNeighborhood (n bits : Nat) (i : Fin n) : Bool := bits.testBit i.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_neighborhoods_complete : ∀ n : Fin 7, ∀ b : Fin n.val → Bool,
    ∃ k : Fin (2 ^ n.val), maskNeighborhood n.val k.val = b := by decide +kernel

structure AtlasWitness where
  target : Nat
  permutation : Nat
  deriving DecidableEq

def atlasWitnessMap (n code : Nat) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨((code / 8 ^ i.val) % 8) % (n + 1), Nat.mod_lt _ (by omega)⟩

def atlasWitnessCheck (n source bits : Nat) (w : AtlasWitness) : Bool :=
  decide (Function.Injective (atlasWitnessMap n w.permutation)) &&
  decide (∀ i j : Fin (n + 1),
    (maskGraph (n + 1) w.target).adj
        (atlasWitnessMap n w.permutation i) (atlasWitnessMap n w.permutation j) =
      (extendGraph (maskGraph n source) (maskNeighborhood n bits)).adj i j)

theorem atlasWitnessCheck_sound {n source bits : Nat} {w : AtlasWitness}
    (hw : atlasWitnessCheck n source bits w = true) :
    Nonempty (BooleanGraphEquiv
      (extendGraph (maskGraph n source) (maskNeighborhood n bits)) (maskGraph (n + 1) w.target)) := by
  simp only [atlasWitnessCheck, Bool.and_eq_true_iff, decide_eq_true_eq] at hw
  exact ⟨⟨Equiv.ofBijective (atlasWitnessMap n w.permutation)
    ⟨hw.1, Finite.surjective_of_injective hw.1⟩, hw.2⟩⟩

structure AtlasRow (n : Nat) where
  source : Nat
  witnesses : Fin (2 ^ n) → AtlasWitness

def atlasRowCheck (n : Nat) (next : List Nat) (row : AtlasRow n) : Bool :=
  (List.finRange (2 ^ n)).all (fun k =>
    next.contains (row.witnesses k).target &&
      atlasWitnessCheck n row.source k.val (row.witnesses k))

theorem atlasRowCheck_sound {n : Nat} (hn : n < 7) {next : List Nat} {row : AtlasRow n}
    (hr : atlasRowCheck n next row = true) (b : Fin n → Bool) :
    ∃ k ∈ next, Nonempty (BooleanGraphEquiv
      (extendGraph (maskGraph n row.source) b) (maskGraph (n + 1) k)) := by
  obtain ⟨bits, hbits⟩ := small_neighborhoods_complete ⟨n, hn⟩ b
  have h := (List.all_eq_true.mp hr) bits (by simp)
  simp only [Bool.and_eq_true_iff, List.contains_iff_mem] at h
  refine ⟨(row.witnesses bits).target, h.1, ?_⟩
  have hi := atlasWitnessCheck_sound h.2
  rw [hbits] at hi
  exact hi

theorem atlasExtends_of_rows {n : Nat} (hn : n < 7) {previous next : List Nat}
    (rows : List (AtlasRow n)) (hs : rows.map AtlasRow.source = previous)
    (hc : rows.all (atlasRowCheck n next) = true) : AtlasExtends n previous next := by
  intro m hm b
  rw [← hs] at hm
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
  exact atlasRowCheck_sound hn ((List.all_eq_true.mp hc) row hr) b

end InducedPentagons.Paper

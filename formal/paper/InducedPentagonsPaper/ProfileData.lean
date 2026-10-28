import InducedPentagonsPaper.PentagonCount
import InducedPentagonsPaper.BooleanPatternBound

/-! Graph-defined induced four-vertex paths and the rooted Clebsch profile.
A path is ordered along its edges, with the smaller endpoint first. -/

namespace InducedPentagons.Paper

structure PathTuple (n : Nat) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  deriving Repr, BEq, DecidableEq

def IsInducedPath {n : Nat} (g : Graph (Fin n)) (p : PathTuple n) : Prop :=
  [p.a, p.b, p.c, p.d].Nodup ∧
  g.adj p.a p.b = true ∧ g.adj p.b p.c = true ∧ g.adj p.c p.d = true ∧
  g.adj p.a p.c = false ∧ g.adj p.a p.d = false ∧ g.adj p.b p.d = false

instance {n : Nat} (g : Graph (Fin n)) (p : PathTuple n) : Decidable (IsInducedPath g p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def normalizedPath {n : Nat} (g : Graph (Fin n)) (p : PathTuple n) : Bool :=
  decide (p.a < p.d) && decide (IsInducedPath g p)

def candidatePaths {n : Nat} (g : Graph (Fin n)) : List (PathTuple n) :=
  (List.finRange n).flatMap fun a =>
    (neighbors g a).flatMap fun b =>
      (neighbors g b).flatMap fun c =>
        (neighbors g c).map fun d => ⟨a, b, c, d⟩

def inducedPaths {n : Nat} (g : Graph (Fin n)) : List (PathTuple n) :=
  (candidatePaths g).filter (normalizedPath g)

theorem mem_inducedPaths {n : Nat} (g : Graph (Fin n)) (p : PathTuple n) :
    p ∈ inducedPaths g ↔ p.a < p.d ∧ IsInducedPath g p := by
  constructor
  · intro h
    have hp := Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2
    exact ⟨of_decide_eq_true hp.1, of_decide_eq_true hp.2⟩
  · intro h
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [normalizedPath, h.1, h.2]⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.a, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.b, (mem_neighbors g p.a p.b).mpr h.2.2.1, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.c, (mem_neighbors g p.b p.c).mpr h.2.2.2.1, ?_⟩
    exact List.mem_map.mpr ⟨p.d, (mem_neighbors g p.c p.d).mpr h.2.2.2.2.1, rfl⟩

theorem candidatePaths_nodup {n : Nat} (g : Graph (Fin n)) : (candidatePaths g).Nodup := by
  have hn : ∀ u, (neighbors g u).Nodup := fun u => (List.nodup_finRange n).filter _
  unfold candidatePaths
  apply nodup_tagged_flatMap _ _ (fun p => p.a) (List.nodup_finRange n)
  · intro a
    apply nodup_tagged_flatMap _ _ (fun p => p.b) (hn a)
    · intro b
      apply nodup_tagged_flatMap _ _ (fun p => p.c) (hn b)
      · intro c
        exact (hn c).map (fun d e h => by injection h)
      · intro c p hp
        rcases List.mem_map.mp hp with ⟨d, _, rfl⟩
        rfl
    · intro b p hp
      simp only [List.mem_flatMap, List.mem_map] at hp
      rcases hp with ⟨c, _, d, _, rfl⟩
      rfl
  · intro a p hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    rcases hp with ⟨b, _, c, _, d, _, rfl⟩
    rfl

theorem inducedPaths_nodup {n : Nat} (g : Graph (Fin n)) : (inducedPaths g).Nodup :=
  (candidatePaths_nodup g).filter _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clebsch_inducedPaths_count : (inducedPaths clebsch).length = 480 := by decide +kernel

def pathLiteral {n : Nat} (p : PathTuple n) (i : Fin n) : Option Bool :=
  if i == p.a || i == p.d then some true
  else if i == p.b || i == p.c then some false
  else none

noncomputable def profileDegree (x : Fin 16 → ℝ) : ℝ := ∑ i, x i

noncomputable def profileLink (x : Fin 16 → ℝ) : ℝ :=
  ((inducedPaths clebsch).map (fun p => patternValue (pathLiteral p) x)).sum

end InducedPentagons.Paper

import InducedPentagonsPaper.PatternSemantics

/-! Encode finite Boolean graphs using the certificate's lexicographic pair bits. -/

namespace InducedPentagons.Paper

def upperPairs (n : Nat) : List (Fin n × Fin n) :=
  (patternPairs n).filter (fun e => decide (e.1.val < e.2.val))

@[simp] theorem mem_upperPairs {n : Nat} (e : Fin n × Fin n) :
    e ∈ upperPairs n ↔ e.1.val < e.2.val := by
  simp [upperPairs, mem_patternPairs]

def rawGraphEncoding {n : Nat} (g : Graph (Fin n)) : Nat :=
  ((upperPairs n).map (fun e => if g.adj e.1 e.2 then
    2 ^ atlasEdgeIndex n e.1.val e.2.val else 0)).foldr (· ||| ·) 0

theorem foldr_or_testBit (xs : List Nat) (k : Nat) :
    (xs.foldr (· ||| ·) 0).testBit k = xs.any (fun x => x.testBit k) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [Nat.testBit_or, ih]

theorem rawGraphEncoding_testBit {n : Nat} (g : Graph (Fin n)) (k : Nat) :
    (rawGraphEncoding g).testBit k = true ↔
      ∃ e ∈ upperPairs n, g.adj e.1 e.2 = true ∧
        atlasEdgeIndex n e.1.val e.2.val = k := by
  rw [rawGraphEncoding, foldr_or_testBit, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hk⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    cases hg : g.adj e.1 e.2 with
    | false => simp [hg] at hk
    | true => exact ⟨e, he, hg, by simpa [hg, Nat.testBit_two_pow] using hk⟩
  · rintro ⟨e, he, hg, hk⟩
    exact ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩, by simp [hg, hk]⟩

def EdgeIndexSeparated (n : Nat) : Prop :=
  ∀ e ∈ upperPairs n, ∀ f ∈ upperPairs n,
    atlasEdgeIndex n e.1.val e.2.val = atlasEdgeIndex n f.1.val f.2.val → e = f

def EdgeIndexBounded (n bits : Nat) : Prop :=
  ∀ e ∈ upperPairs n, atlasEdgeIndex n e.1.val e.2.val < bits

theorem rawGraphEncoding_at_pair {n : Nat} (hs : EdgeIndexSeparated n)
    (g : Graph (Fin n)) (i j : Fin n) (hij : i.val < j.val) :
    (rawGraphEncoding g).testBit (atlasEdgeIndex n i.val j.val) = g.adj i j := by
  apply Bool.eq_iff_iff.mpr
  rw [rawGraphEncoding_testBit]
  constructor
  · rintro ⟨e, he, hg, hk⟩
    have heq := hs e he (i, j) (mem_upperPairs _ |>.mpr hij) hk
    simpa [heq] using hg
  · intro hg
    exact ⟨(i, j), (mem_upperPairs _).mpr hij, hg, rfl⟩

def graphEncoding {n : Nat} (bits : Nat) (g : Graph (Fin n)) : Fin (2 ^ bits) :=
  ⟨rawGraphEncoding g % 2 ^ bits, Nat.mod_lt _ (by positivity)⟩

theorem graphEncoding_congr {n bits : Nat} {g h : Graph (Fin n)}
    (he : ∀ i j, g.adj i j = h.adj i j) : graphEncoding bits g = graphEncoding bits h := by
  apply Fin.ext
  simp only [graphEncoding, rawGraphEncoding, he]

theorem graphEncoding_adj {n bits : Nat} (hs : EdgeIndexSeparated n)
    (hb : EdgeIndexBounded n bits) (g : Graph (Fin n)) :
    ∀ i j, (maskGraph n (graphEncoding bits g).val).adj i j = g.adj i j := by
  intro i j
  by_cases heq : i = j
  · subst j
    simp [Graph.loopless]
  have hval : i.val ≠ j.val := fun h => heq (Fin.ext h)
  have forward (i j : Fin n) (hij : i.val < j.val) :
      (maskGraph n (graphEncoding bits g).val).adj i j = g.adj i j := by
    have hbound := hb (i, j) ((mem_upperPairs _).mpr hij)
    simp only [maskGraph, graphEncoding, Nat.min_eq_left (Nat.le_of_lt hij),
      Nat.max_eq_right (Nat.le_of_lt hij), ne_eq, Nat.ne_of_lt hij, not_false_eq_true,
      decide_true, Bool.true_and, Nat.testBit_mod_two_pow, hbound]
    simpa using rawGraphEncoding_at_pair hs g i j hij
  rcases lt_or_gt_of_ne hval with hij | hji
  · exact forward i j hij
  · rw [(maskGraph n (graphEncoding bits g).val).symmetric, g.symmetric i j]
    exact forward j i hji

theorem graphEncoding_equiv {n bits : Nat} (hs : EdgeIndexSeparated n)
    (hb : EdgeIndexBounded n bits) (g : Graph (Fin n)) :
    Nonempty (BooleanGraphEquiv g (maskGraph n (graphEncoding bits g).val)) :=
  ⟨⟨Equiv.refl _, graphEncoding_adj hs hb g⟩⟩

theorem edgeIndexSeparated_four : EdgeIndexSeparated 4 := by
  unfold EdgeIndexSeparated
  decide +kernel
theorem edgeIndexBounded_four : EdgeIndexBounded 4 6 := by
  unfold EdgeIndexBounded
  decide +kernel
theorem edgeIndexSeparated_five : EdgeIndexSeparated 5 := by
  unfold EdgeIndexSeparated
  decide +kernel
theorem edgeIndexBounded_five : EdgeIndexBounded 5 10 := by
  unfold EdgeIndexBounded
  decide +kernel

end InducedPentagons.Paper

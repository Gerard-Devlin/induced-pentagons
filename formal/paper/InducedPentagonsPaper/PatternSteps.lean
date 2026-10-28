import InducedPentagonsPaper.PatternEnumeration

/-! Check only the constraints whose larger endpoint is newly assigned. -/

namespace InducedPentagons.Paper

def OrderedPattern {k : Nat} (p : PartialPattern k) : Prop :=
  (∀ e ∈ p.edges, e.1.val < e.2.val) ∧ (∀ e ∈ p.nonedges, e.1.val < e.2.val)

def stepMatches {k n m : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin m → Fin n) (v : Fin n) : Bool :=
  (p.edges.filter (fun e => decide (e.2.val = m))).all
    (fun e => if hi : e.1.val < m then g.adj (f ⟨e.1.val, hi⟩) v else false) &&
  (p.nonedges.filter (fun e => decide (e.2.val = m))).all
    (fun e => if hi : e.1.val < m then !(g.adj (f ⟨e.1.val, hi⟩) v) else false)

theorem extendPrefix_at_lt {m n : Nat} (f : Fin m → Fin n) (v : Fin n)
    (i : Fin (m + 1)) (hi : i.val < m) : extendPrefix f v i = f ⟨i.val, hi⟩ := by
  simp [extendPrefix, hi]

theorem extendPrefix_at_last {m n : Nat} (f : Fin m → Fin n) (v : Fin n)
    (i : Fin (m + 1)) (hi : i.val = m) : extendPrefix f v i = v := by
  have he : i = Fin.last m := Fin.ext hi
  rw [he, extendPrefix_last]

theorem stepMatches_iff_prefix {k n m : Nat} {p : PartialPattern k} {g : Graph (Fin n)}
    (hp : OrderedPattern p) {f : Fin m → Fin n} (hf : PrefixSatisfies p g f) (v : Fin n) :
    stepMatches p g f v = true ↔ PrefixSatisfies p g (extendPrefix f v) := by
  simp only [stepMatches, Bool.and_eq_true_iff, List.all_eq_true]
  constructor
  · rintro ⟨he, hn⟩
    constructor
    · intro e hmem hi hj
      have horder := hp.1 e hmem
      by_cases hlast : e.2.val = m
      · have hleft : e.1.val < m := by omega
        rw [extendPrefix_at_lt f v _ hleft, extendPrefix_at_last f v _ hlast]
        simpa [hleft] using he e (List.mem_filter.mpr ⟨hmem, by simpa using hlast⟩)
      · have hright : e.2.val < m := by omega
        have hleft : e.1.val < m := by omega
        rw [extendPrefix_at_lt f v _ hleft, extendPrefix_at_lt f v _ hright]
        exact hf.1 e hmem hleft hright
    · intro e hmem hi hj
      have horder := hp.2 e hmem
      by_cases hlast : e.2.val = m
      · have hleft : e.1.val < m := by omega
        rw [extendPrefix_at_lt f v _ hleft, extendPrefix_at_last f v _ hlast]
        simpa [hleft] using hn e (List.mem_filter.mpr ⟨hmem, by simpa using hlast⟩)
      · have hright : e.2.val < m := by omega
        have hleft : e.1.val < m := by omega
        rw [extendPrefix_at_lt f v _ hleft, extendPrefix_at_lt f v _ hright]
        exact hf.2 e hmem hleft hright
  · intro hs
    constructor
    · intro e hmem
      obtain ⟨he, hlast⟩ := List.mem_filter.mp hmem
      have hlast' : e.2.val = m := by simpa using hlast
      have horder := hp.1 e he
      have hleft : e.1.val < m := by omega
      have h := hs.1 e he (by omega) (by omega)
      rw [extendPrefix_at_lt f v _ hleft, extendPrefix_at_last f v _ hlast'] at h
      simpa [hleft] using h
    · intro e hmem
      obtain ⟨he, hlast⟩ := List.mem_filter.mp hmem
      have hlast' : e.2.val = m := by simpa using hlast
      have horder := hp.2 e he
      have hleft : e.1.val < m := by omega
      have h := hs.2 e he (by omega) (by omega)
      rw [extendPrefix_at_lt f v _ hleft, extendPrefix_at_last f v _ hlast'] at h
      simpa [hleft] using h

def fastPatternPrefixes {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    (m : Nat) → List (Fin m → Fin n)
  | 0 => [fun i => Fin.elim0 i]
  | m + 1 => (fastPatternPrefixes p g m).flatMap (fun f =>
      ((List.finRange n).filter (fun v => prefixAvoids f v && stepMatches p g f v)).map
        (fun v => extendPrefix f v))

theorem fastPatternPrefixes_eq {k n : Nat} {p : PartialPattern k} (hp : OrderedPattern p)
    (g : Graph (Fin n)) : ∀ m, fastPatternPrefixes p g m = patternPrefixes p g m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [fastPatternPrefixes, patternPrefixes, ih]
    apply List.flatMap_congr
    intro f hf
    apply congrArg (List.map (fun v => extendPrefix f v))
    apply List.filter_congr
    intro v _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true_iff]
    rw [stepMatches_iff_prefix hp ((mem_patternPrefixes p g m f).mp hf).2,
      prefixMatches_iff]

def fastPatternEnumeration {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    List (Fin k → Fin n) := fastPatternPrefixes p g k

theorem fastPatternEnumeration_count {k n : Nat} {p : PartialPattern k} (hp : OrderedPattern p)
    (g : Graph (Fin n)) :
    patternInjectionCount p g = (fastPatternEnumeration p g).length := by
  rw [fastPatternEnumeration, fastPatternPrefixes_eq hp]
  exact patternInjectionCount_eq_enumeration_length p g

end InducedPentagons.Paper

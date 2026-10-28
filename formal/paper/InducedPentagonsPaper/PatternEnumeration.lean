import InducedPentagonsPaper.PatternSemantics

/-! Complete duplicate-free pattern injection enumeration with prefix pruning. -/

namespace InducedPentagons.Paper

def PrefixSatisfies {k n m : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin m → Fin n) : Prop :=
  (∀ e ∈ p.edges, ∀ hi : e.1.val < m, ∀ hj : e.2.val < m,
    g.adj (f ⟨e.1.val, hi⟩) (f ⟨e.2.val, hj⟩) = true) ∧
  (∀ e ∈ p.nonedges, ∀ hi : e.1.val < m, ∀ hj : e.2.val < m,
    g.adj (f ⟨e.1.val, hi⟩) (f ⟨e.2.val, hj⟩) = false)

def prefixMatches {k n m : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin m → Fin n) : Bool :=
  p.edges.all (fun e => if hi : e.1.val < m then
    if hj : e.2.val < m then g.adj (f ⟨e.1.val, hi⟩) (f ⟨e.2.val, hj⟩) else true
    else true) &&
  p.nonedges.all (fun e => if hi : e.1.val < m then
    if hj : e.2.val < m then !(g.adj (f ⟨e.1.val, hi⟩) (f ⟨e.2.val, hj⟩)) else true
    else true)

theorem prefixMatches_iff {k n m : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin m → Fin n) : prefixMatches p g f = true ↔ PrefixSatisfies p g f := by
  simp only [prefixMatches, PrefixSatisfies, Bool.and_eq_true_iff, List.all_eq_true]
  constructor
  · rintro ⟨he, hn⟩
    constructor
    · intro e hmem hi hj
      simpa [hi, hj] using he e hmem
    · intro e hmem hi hj
      simpa [hi, hj] using hn e hmem
  · rintro ⟨he, hn⟩
    constructor
    · intro e hmem
      split_ifs with hi hj
      · exact he e hmem hi hj
      · rfl
      · rfl
    · intro e hmem
      split_ifs with hi hj
      · simpa using hn e hmem hi hj
      · rfl
      · rfl

theorem prefixSatisfies_zero {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin 0 → Fin n) : PrefixSatisfies p g f := by
  constructor <;> intro e _ hi <;> omega

theorem prefixSatisfies_restrict {k n m : Nat} {p : PartialPattern k} {g : Graph (Fin n)}
    {f : Fin (m + 1) → Fin n} (hf : PrefixSatisfies p g f) :
    PrefixSatisfies p g (fun i : Fin m => f i.castSucc) := by
  constructor
  · intro e he hi hj
    exact hf.1 e he (by omega) (by omega)
  · intro e he hi hj
    exact hf.2 e he (by omega) (by omega)

theorem prefixSatisfies_full_iff {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin k → Fin n) : PrefixSatisfies p g f ↔ PatternSatisfies p g f := by
  constructor
  · intro h
    exact ⟨fun e he => h.1 e he e.1.isLt e.2.isLt,
      fun e he => h.2 e he e.1.isLt e.2.isLt⟩
  · intro h
    exact ⟨fun e he _ _ => h.1 e he, fun e he _ _ => h.2 e he⟩

def extendPrefix {m n : Nat} (f : Fin m → Fin n) (v : Fin n) (i : Fin (m + 1)) : Fin n :=
  if hi : i.val < m then f ⟨i.val, hi⟩ else v

@[simp] theorem extendPrefix_castSucc {m n : Nat} (f : Fin m → Fin n) (v : Fin n)
    (i : Fin m) : extendPrefix f v i.castSucc = f i := by simp [extendPrefix]

@[simp] theorem extendPrefix_last {m n : Nat} (f : Fin m → Fin n) (v : Fin n) :
    extendPrefix f v (Fin.last m) = v := by simp [extendPrefix]

theorem extendPrefix_reconstruct {m n : Nat} (f : Fin (m + 1) → Fin n) :
    extendPrefix (fun i : Fin m => f i.castSucc) (f (Fin.last m)) = f := by
  funext i
  induction i using Fin.lastCases <;> simp

theorem extendPrefix_injective_iff {m n : Nat} (f : Fin m → Fin n) (v : Fin n) :
    Function.Injective (extendPrefix f v) ↔ Function.Injective f ∧ ∀ i, f i ≠ v := by
  constructor
  · intro h
    constructor
    · intro i j hij
      apply Fin.castSucc_inj.mp
      exact h (by simpa using hij)
    · intro i hi
      have he : i.castSucc = Fin.last m := h (by simpa using hi)
      have hv := congrArg Fin.val he
      have hil := i.isLt
      simp at hv
      omega
  · rintro ⟨hf, hv⟩ i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · rfl
    · exact False.elim (hv _ (by simpa using hij.symm))
    · exact False.elim (hv _ (by simpa using hij))
    · exact congrArg Fin.castSucc (hf (by simpa using hij))

def prefixAvoids {m n : Nat} (f : Fin m → Fin n) (v : Fin n) : Bool :=
  (List.finRange m).all (fun i => decide (f i ≠ v))

theorem prefixAvoids_iff {m n : Nat} (f : Fin m → Fin n) (v : Fin n) :
    prefixAvoids f v = true ↔ ∀ i, f i ≠ v := by
  simp [prefixAvoids, List.all_eq_true]

def patternPrefixes {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    (m : Nat) → List (Fin m → Fin n)
  | 0 => [fun i => Fin.elim0 i]
  | m + 1 => (patternPrefixes p g m).flatMap (fun f =>
      ((List.finRange n).filter (fun v => prefixAvoids f v &&
        prefixMatches p g (extendPrefix f v))).map (fun v => extendPrefix f v))

theorem mem_patternPrefixes {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    ∀ m (f : Fin m → Fin n), f ∈ patternPrefixes p g m ↔
      Function.Injective f ∧ PrefixSatisfies p g f := by
  intro m
  induction m with
  | zero =>
    intro f
    constructor
    · intro _
      exact ⟨fun i => Fin.elim0 i, prefixSatisfies_zero p g f⟩
    · intro _
      have he : f = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
      simp [patternPrefixes, he]
  | succ m ih =>
    intro f
    constructor
    · intro hf
      simp only [patternPrefixes, List.mem_flatMap, List.mem_map, List.mem_filter,
        Bool.and_eq_true_iff] at hf
      obtain ⟨q, hq, v, ⟨_, hav, hmatch⟩, rfl⟩ := hf
      exact ⟨(extendPrefix_injective_iff q v).mpr
        ⟨((ih q).mp hq).1, (prefixAvoids_iff q v).mp hav⟩,
        (prefixMatches_iff p g _).mp hmatch⟩
    · rintro ⟨hinj, hmatch⟩
      let q : Fin m → Fin n := fun i => f i.castSucc
      let v := f (Fin.last m)
      have hrec : extendPrefix q v = f := extendPrefix_reconstruct f
      have hqinj : Function.Injective q := by
        intro i j hij
        exact Fin.castSucc_inj.mp (hinj hij)
      have hq : q ∈ patternPrefixes p g m :=
        (ih q).mpr ⟨hqinj, prefixSatisfies_restrict hmatch⟩
      apply List.mem_flatMap.mpr
      refine ⟨q, hq, List.mem_map.mpr ⟨v, ?_, hrec⟩⟩
      apply List.mem_filter.mpr
      refine ⟨by simp, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
      · apply (prefixAvoids_iff q v).mpr
        have hh := (extendPrefix_injective_iff q v).mp (hrec.symm ▸ hinj)
        exact hh.2
      · apply (prefixMatches_iff p g _).mpr
        exact hrec.symm ▸ hmatch

theorem patternPrefixes_nodup {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    ∀ m, (patternPrefixes p g m).Nodup := by
  intro m
  induction m with
  | zero => simp [patternPrefixes]
  | succ m ih =>
    unfold patternPrefixes
    apply nodup_tagged_flatMap _ _ (fun f => fun i : Fin m => f i.castSucc) ih
    · intro f
      apply List.Nodup.map _ ((List.nodup_finRange n).filter _)
      intro v w hvw
      simpa using congrFun hvw (Fin.last m)
    · intro f q hq
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
      funext i
      simp

def patternInjectionEnumeration {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    List (Fin k → Fin n) := patternPrefixes p g k

theorem mem_patternInjectionEnumeration {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin k → Fin n) : f ∈ patternInjectionEnumeration p g ↔
      Function.Injective f ∧ PatternSatisfies p g f := by
  rw [patternInjectionEnumeration, mem_patternPrefixes, prefixSatisfies_full_iff]

def patternEnumerationEquiv {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    PatternInjection p g ≃ ↥(patternInjectionEnumeration p g).toFinset where
  toFun f := ⟨f.val, List.mem_toFinset.mpr ((mem_patternInjectionEnumeration p g f.val).mpr f.property)⟩
  invFun f := ⟨f.val, (mem_patternInjectionEnumeration p g f.val).mp (List.mem_toFinset.mp f.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem patternInjectionCount_eq_enumeration_length {k n : Nat} (p : PartialPattern k)
    (g : Graph (Fin n)) : patternInjectionCount p g = (patternInjectionEnumeration p g).length := by
  rw [patternInjectionCount, Fintype.card_congr (patternEnumerationEquiv p g), Fintype.card_coe]
  exact List.toFinset_card_of_nodup (patternPrefixes_nodup p g k)

end InducedPentagons.Paper

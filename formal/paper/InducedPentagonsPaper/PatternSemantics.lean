import InducedPentagonsPaper.FiniteAtlas
import InducedPentagonsPaper.CycleSymmetry

/-! Required-edge/nonedge patterns and their finite injection semantics. -/

open scoped BigOperators

namespace InducedPentagons.Paper

structure PartialPattern (k : Nat) where
  edges : List (Fin k × Fin k)
  nonedges : List (Fin k × Fin k)

def PatternSatisfies {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n))
    (f : Fin k → Fin n) : Prop :=
  (∀ e ∈ p.edges, g.adj (f e.1) (f e.2) = true) ∧
  (∀ e ∈ p.nonedges, g.adj (f e.1) (f e.2) = false)

def PatternInjection {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :=
  {f : Fin k → Fin n // Function.Injective f ∧ PatternSatisfies p g f}

instance {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) (f : Fin k → Fin n) :
    Decidable (PatternSatisfies p g f) := inferInstanceAs
  (Decidable ((∀ e ∈ p.edges, g.adj (f e.1) (f e.2) = true) ∧
    (∀ e ∈ p.nonedges, g.adj (f e.1) (f e.2) = false)))

instance {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) :
    Fintype (PatternInjection p g) := inferInstanceAs
  (Fintype {f : Fin k → Fin n // (∀ i j : Fin k, f i = f j → i = j) ∧
    PatternSatisfies p g f})

def BooleanGraphEquiv.symm {V W : Type} {g : Graph V} {h : Graph W}
    (e : BooleanGraphEquiv g h) : BooleanGraphEquiv h g :=
  ⟨e.val.symm, by
    intro u v
    have he := e.property (e.val.symm u) (e.val.symm v)
    simpa using he.symm⟩

theorem patternSatisfies_comp_equiv_iff {k n m : Nat} (p : PartialPattern k)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) (f : Fin k → Fin n) :
    PatternSatisfies p h (e.val ∘ f) ↔ PatternSatisfies p g f := by
  simp only [PatternSatisfies, Function.comp_apply, e.property]

def patternInjectionEquiv {k n m : Nat} (p : PartialPattern k)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    PatternInjection p g ≃ PatternInjection p h where
  toFun f := ⟨e.val ∘ f.val, e.val.injective.comp f.property.1,
    (patternSatisfies_comp_equiv_iff p e f.val).mpr f.property.2⟩
  invFun f := ⟨e.val.symm ∘ f.val, e.val.symm.injective.comp f.property.1,
    (patternSatisfies_comp_equiv_iff p e.symm f.val).mpr f.property.2⟩
  left_inv f := Subtype.ext (funext (fun i => e.val.symm_apply_apply (f.val i)))
  right_inv f := Subtype.ext (funext (fun i => e.val.apply_symm_apply (f.val i)))

def patternInjectionCount {k n : Nat} (p : PartialPattern k) (g : Graph (Fin n)) : Nat :=
  Fintype.card (PatternInjection p g)

theorem patternInjectionCount_isomorphic {k n m : Nat} (p : PartialPattern k)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) :
    patternInjectionCount p g = patternInjectionCount p h :=
  Fintype.card_congr (patternInjectionEquiv p e)

def patternPairs (k : Nat) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap (fun i => (List.finRange k).map (fun j => (i, j)))

theorem mem_patternPairs {k : Nat} (e : Fin k × Fin k) : e ∈ patternPairs k := by
  simp [patternPairs]

def completePattern {k : Nat} (g : Graph (Fin k)) : PartialPattern k where
  edges := (patternPairs k).filter (fun e => g.adj e.1 e.2)
  nonedges := (patternPairs k).filter (fun e => !(g.adj e.1 e.2))

theorem satisfies_completePattern_iff {k n : Nat} (h : Graph (Fin k)) (g : Graph (Fin n))
    (f : Fin k → Fin n) :
    PatternSatisfies (completePattern h) g f ↔ ∀ i j, g.adj (f i) (f j) = h.adj i j := by
  constructor
  · intro hp i j
    cases hh : h.adj i j with
    | false =>
      exact hp.2 (i, j) (List.mem_filter.mpr ⟨mem_patternPairs _, by simp [hh]⟩)
    | true =>
      exact hp.1 (i, j) (List.mem_filter.mpr ⟨mem_patternPairs _, hh⟩)
  · intro hp
    constructor
    · intro e he
      exact (hp e.1 e.2).trans (List.mem_filter.mp he).2
    · intro e he
      have hn := (List.mem_filter.mp he).2
      have hh : h.adj e.1 e.2 = false := by simpa using hn
      exact (hp e.1 e.2).trans hh

def pentagonPattern : PartialPattern 5 := completePattern cycleGraph

theorem pentagonPattern_satisfies_iff {n : Nat} (g : Graph (Fin n)) (f : Fin 5 → Fin n) :
    PatternSatisfies pentagonPattern g f ↔ IsInducedPentagon g f :=
  satisfies_completePattern_iff cycleGraph g f

def pentagonPatternEquiv {n : Nat} (g : Graph (Fin n)) :
    PatternInjection pentagonPattern g ≃ PentagonEmbedding g where
  toFun f := ⟨f.val, (pentagonPattern_satisfies_iff g f.val).mp f.property.2⟩
  invFun f := ⟨f.val, inducedPentagon_injective f.property,
    (pentagonPattern_satisfies_iff g f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pentagonPattern_count {n : Nat} (g : Graph (Fin n)) :
    patternInjectionCount pentagonPattern g = Fintype.card (PentagonEmbedding g) :=
  Fintype.card_congr (pentagonPatternEquiv g)

noncomputable def patternInjectionWeight {k n : Nat} (p : PartialPattern k)
    (g : Graph (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∑ f : PatternInjection p g, ∏ i, x (f.val i)

theorem patternInjectionWeight_isomorphic {k n m : Nat} (p : PartialPattern k)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h) (x : Fin m → ℝ) :
    patternInjectionWeight p g (x ∘ e.val) = patternInjectionWeight p h x := by
  unfold patternInjectionWeight
  exact Fintype.sum_equiv (patternInjectionEquiv p e) _ _ (fun _ => rfl)

theorem pentagonPattern_weight {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) :
    patternInjectionWeight pentagonPattern g x = 10 * pentagonMass g x := by
  have h := Fintype.sum_equiv (pentagonPatternEquiv g)
    (fun f => ∏ i, x (f.val i)) (fun f => ∏ i, x (f.val i)) (fun _ => rfl)
  unfold patternInjectionWeight pentagonMass
  rw [h]
  ring

end InducedPentagons.Paper

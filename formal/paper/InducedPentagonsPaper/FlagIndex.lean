import InducedPentagonsPaper.RootedClassification

/-! Checked rooted-graph classifiers with indices in the actual tensor basis. -/

namespace InducedPentagons.Paper

structure IndexedFlagWitness (dimension : Nat) where
  witness : RootedFlagWitness
  index : Fin dimension

def flagIndexLookupCheck {dimension : Nat} (n bits roots typeMask : Nat)
    (basis : Vector Nat dimension) (lookup : Fin (2 ^ bits) → IndexedFlagWitness dimension) : Bool :=
  rootedLookupCheck n bits roots typeMask basis.toList (fun m => (lookup m).witness) &&
  (List.finRange (2 ^ bits)).all (fun m =>
    if rootTypeCheck roots typeMask (maskGraph n m.val) then
      decide ((lookup m).witness.target = basis[(lookup m).index])
    else true)

def flagIndex {dimension n : Nat} (bits : Nat)
    (lookup : Fin (2 ^ bits) → IndexedFlagWitness dimension) (g : Graph (Fin n)) : Fin dimension :=
  (lookup (graphEncoding bits g)).index

theorem flagIndexBasis_mem {dimension : Nat} (basis : Vector Nat dimension) (i : Fin dimension) :
    basis[i] ∈ basis.toList := by
  simp only [Fin.getElem_fin, Vector.mem_toList_iff]
  exact Vector.getElem_mem i.isLt

theorem flagIndex_sound {dimension n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    {basis : Vector Nat dimension} {lookup : Fin (2 ^ bits) → IndexedFlagWitness dimension}
    (hc : flagIndexLookupCheck n bits roots typeMask basis lookup = true)
    (g : Graph (Fin n)) (hg : rootTypeCheck roots typeMask g = true) :
    Nonempty (RootedGraphEquiv roots g (maskGraph n basis[flagIndex bits lookup g])) := by
  simp only [flagIndexLookupCheck, Bool.and_eq_true_iff] at hc
  let m := graphEncoding bits g
  have hm : rootTypeCheck roots typeMask (maskGraph n m.val) = true := by
    simpa only [rootTypeCheck, m, graphEncoding_adj hs hb g] using hg
  have hi := (List.all_eq_true.mp hc.2) m (by simp)
  simp only [hm, ite_true, decide_eq_true_eq] at hi
  have ht : rootedClassify bits (fun m => (lookup m).witness) g = basis[flagIndex bits lookup g] := hi
  rw [← ht]
  exact (rootedClassify_sound hs hb hc.1 g hg).2

theorem flagIndex_eq_iff {dimension n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    {basis : Vector Nat dimension} {lookup : Fin (2 ^ bits) → IndexedFlagWitness dimension}
    (hc : flagIndexLookupCheck n bits roots typeMask basis lookup = true)
    (hp : RootedFlagBasisSeparated n roots basis.toList)
    (hn : Function.Injective (fun i : Fin dimension => basis[i]))
    (g : Graph (Fin n)) (hg : rootTypeCheck roots typeMask g = true) (j : Fin dimension) :
    flagIndex bits lookup g = j ↔ Nonempty (RootedGraphEquiv roots g (maskGraph n basis[j])) := by
  obtain ⟨e⟩ := flagIndex_sound hs hb hc g hg
  constructor
  · rintro he
    rw [← he]
    exact ⟨e⟩
  · rintro ⟨f⟩
    apply hn
    exact hp _ (flagIndexBasis_mem basis _) _ (flagIndexBasis_mem basis _) ⟨e.symm.trans f⟩

theorem flagIndex_isomorphic {dimension n bits roots typeMask : Nat}
    (hs : EdgeIndexSeparated n) (hb : EdgeIndexBounded n bits)
    {basis : Vector Nat dimension} {lookup : Fin (2 ^ bits) → IndexedFlagWitness dimension}
    (hc : flagIndexLookupCheck n bits roots typeMask basis lookup = true)
    (hp : RootedFlagBasisSeparated n roots basis.toList)
    (hn : Function.Injective (fun i : Fin dimension => basis[i]))
    {g h : Graph (Fin n)} (hg : rootTypeCheck roots typeMask g = true)
    (hh : rootTypeCheck roots typeMask h = true) (e : RootedGraphEquiv roots g h) :
    flagIndex bits lookup g = flagIndex bits lookup h := by
  obtain ⟨f⟩ := flagIndex_sound hs hb hc h hh
  exact (flagIndex_eq_iff hs hb hc hp hn g hg _).mpr ⟨e.trans f⟩

end InducedPentagons.Paper

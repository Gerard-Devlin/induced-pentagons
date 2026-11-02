import InducedPentagonsPaper.FixedDensityCertificate

/-! Integer encodings of invariant count signatures and linear-time separation checks. -/

namespace InducedPentagons.Paper

def hostSignatureCode (values : List Nat) : Nat := values.foldr (fun v rest => v + 8192 * rest) 0

def graphCountCode {n : Nat} (g : Graph (Fin n)) : Nat :=
  hostSignatureCode (primitiveSemanticCounts primitivePatternSpecs g ++
    fixedDensityCounts g ++ fixedComplementCounts g)

def rowCountCode (h : HostRow) : Nat :=
  hostSignatureCode (h.primitive.toList ++ h.induced.toList ++ h.complement.toList)

def rowCountPairs : List (Nat × Nat) := primitiveCertificateRows.map (fun h => (h.mask, rowCountCode h))

theorem graphCountCode_isomorphic {n m : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) : graphCountCode g = graphCountCode h := by
  unfold graphCountCode
  rw [primitiveSemanticCounts_isomorphic primitivePatternSpecs e,
    fixedDensityCounts_isomorphic e, fixedComplementCounts_isomorphic e]

theorem rowCountCode_semantics (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    rowCountCode h = graphCountCode (maskGraph 7 h.mask) := by
  unfold rowCountCode graphCountCode
  rw [primitive_certificate_rows_semantics h hh, fixed_certificate_induced_values h hh,
    fixed_certificate_complement_values h hh]

def increasingHostCodes : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.2 < b.2) && increasingHostCodes (b :: rest)

theorem increasingHostCodes_pairwise (data : List (Nat × Nat))
    (hc : increasingHostCodes data = true) : data.Pairwise (fun a b => a.2 < b.2) := by
  induction data with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b rest =>
      simp only [increasingHostCodes, Bool.and_eq_true_iff, decide_eq_true_eq] at hc
      have ht := ih hc.2
      apply List.pairwise_cons.mpr
      refine ⟨?_, ht⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hc.1
      · exact lt_trans hc.1 ((List.pairwise_cons.mp ht).1 z hz)

theorem pairwiseHostCodes_separate (data : List (Nat × Nat)) :
    data.Pairwise (fun a b => a.2 < b.2) →
      ∀ r ∈ data, ∀ s ∈ data, r.2 = s.2 → r.1 = s.1 := by
  induction data with
  | nil => simp
  | cons a rest ih =>
    intro hp r hr s hs he
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hr with hr | hr
    · rcases List.mem_cons.mp hs with hs | hs
      · exact congrArg Prod.fst (hr.trans hs.symm)
      · have hlt := hhead s hs
        rw [← hr] at hlt
        exact False.elim ((ne_of_lt hlt) he)
    · rcases List.mem_cons.mp hs with hs | hs
      · have hlt := hhead r hr
        rw [← hs] at hlt
        exact False.elim ((ne_of_lt hlt) he.symm)
      · exact ih htail r hr s hs he

theorem increasingHostCodes_separate {data : List (Nat × Nat)}
    (hc : increasingHostCodes data = true) :
    ∀ r ∈ data, ∀ s ∈ data, r.2 = s.2 → r.1 = s.1 :=
  pairwiseHostCodes_separate data (increasingHostCodes_pairwise data hc)

end InducedPentagons.Paper

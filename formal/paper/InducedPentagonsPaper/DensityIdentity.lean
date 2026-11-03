import InducedPentagonsPaper.PrimitiveColumnAlgebra
import InducedPentagonsPaper.HostIdentity
import InducedPentagonsPaper.FixedDensityCertificate

/-! Graph density expressions for the checked certificate columns. -/

namespace InducedPentagons.Paper

/-- Injective density of the specified primitive, with the original ordering. -/
def graphPrimitiveDensity {n : Nat} (g : Graph (Fin n)) (i : Fin 22) : ℚ :=
  (primitiveSemanticDensities primitivePatternSpecs g)[i.val]!

theorem graphPrimitiveDensity_isomorphic {n : Nat} {g h : Graph (Fin n)}
    (e : BooleanGraphEquiv g h) (i : Fin 22) :
    graphPrimitiveDensity g i = graphPrimitiveDensity h i := by
  unfold graphPrimitiveDensity
  rw [primitiveSemanticDensities_isomorphic primitivePatternSpecs e]

theorem graphPrimitiveDensity_certificate (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (i : Fin 22) :
    graphPrimitiveDensity (maskGraph 7 h.mask) i = rowPrimitiveDensity h i.val :=
  primitive_certificate_density_entry h hh i

def semanticFreePrimitiveColumns {n : Nat} (g : Graph (Fin n)) : Array ℚ :=
  #[(5 / 144 : ℚ) * graphPrimitiveDensity g 2 - (5 / 663552 : ℚ) * graphPrimitiveDensity g 5,
    (5 / 144 : ℚ) * graphPrimitiveDensity g 3 - (5 / 663552 : ℚ) * graphPrimitiveDensity g 6,
    (5 / 144 : ℚ) * graphPrimitiveDensity g 4 - (5 / 663552 : ℚ) * graphPrimitiveDensity g 7]

def semanticPositiveColumns {n : Nat} (g : Graph (Fin n)) : Array ℚ :=
  #[(5 / 144 : ℚ) * graphPrimitiveDensity g 8 - (5 / 663552 : ℚ) * graphPrimitiveDensity g 9,
    graphPrimitiveDensity g 11 - graphPrimitiveDensity g 12 -
      (1 / 9216 : ℚ) * graphPrimitiveDensity g 10,
    graphPrimitiveDensity g 14 - graphPrimitiveDensity g 15 -
      (1 / 9216 : ℚ) * graphPrimitiveDensity g 13,
    (1 / 2 : ℚ) * graphPrimitiveDensity g 16 - (1 / 9216 : ℚ) * graphPrimitiveDensity g 21 -
      (1 / 2 : ℚ) * (graphPrimitiveDensity g 17 + graphPrimitiveDensity g 18 +
        graphPrimitiveDensity g 19 + graphPrimitiveDensity g 20)]

theorem freePrimitiveColumns_certificate (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (i : Fin 3) :
    ((freeColumns Generated.certificate h)[i.val]! : ℚ) / 557383680 =
      (semanticFreePrimitiveColumns (maskGraph 7 h.mask))[i.val]! := by
  fin_cases i
  · simpa [semanticFreePrimitiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_free_column0 h
  · simpa [semanticFreePrimitiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_free_column1 h
  · simpa [semanticFreePrimitiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_free_column2 h

theorem positiveColumns_certificate (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (i : Fin 4) :
    ((positiveColumns Generated.certificate h)[i.val]! : ℚ) / 557383680 =
      (semanticPositiveColumns (maskGraph 7 h.mask))[i.val]! := by
  fin_cases i
  · simpa [semanticPositiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_positive_column0 h
  · simpa [semanticPositiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_positive_column1 h
  · simpa [semanticPositiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_positive_column2 h
  · simpa [semanticPositiveColumns, graphPrimitiveDensity_certificate h hh] using primitive_positive_column3 h

theorem semanticFreePrimitiveColumns_isomorphic {n : Nat} {g h : Graph (Fin n)}
    (e : BooleanGraphEquiv g h) : semanticFreePrimitiveColumns g = semanticFreePrimitiveColumns h := by
  simp only [semanticFreePrimitiveColumns, graphPrimitiveDensity_isomorphic e]

theorem semanticPositiveColumns_isomorphic {n : Nat} {g h : Graph (Fin n)}
    (e : BooleanGraphEquiv g h) : semanticPositiveColumns g = semanticPositiveColumns h := by
  simp only [semanticPositiveColumns, graphPrimitiveDensity_isomorphic e]

/-- The 34 fixed columns, defined intrinsically on the graph. -/
def semanticFixedColumn {n : Nat} (g : Graph (Fin n)) (j : Fin 34) : ℚ :=
  fiveTypeComplementDensity g fixedTypeMasks[j.val]! -
    (5 / 144 : ℚ) * fiveTypeDensity g fixedTypeMasks[j.val]!

theorem semanticFixedColumn_isomorphic {n : Nat} {g h : Graph (Fin n)}
    (e : BooleanGraphEquiv g h) (j : Fin 34) :
    semanticFixedColumn g j = semanticFixedColumn h j := by
  have hj : j.val < fixedTypeMasks.length := by rw [fixed_type_masks_count]; exact j.isLt
  have hm : fixedTypeMasks[j.val]! ∈ fixedTypeMasks := by
    rw [getElem!_pos fixedTypeMasks j.val hj]
    exact List.getElem_mem hj
  simp only [semanticFixedColumn, fiveTypeComplementDensity, fiveTypeDensity,
    fixedDensityCount_isomorphic e _ hm, fixedComplementCount_isomorphic e _ hm]

theorem fixedColumn_certificate (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (j : Fin 34) :
    ((freeColumns Generated.certificate h)[j.val + 3]! : ℚ) / 557383680 =
      semanticFixedColumn (maskGraph 7 h.mask) j := by
  simpa [semanticFixedColumn, certificate_data_denominator] using
    fixed_certificate_free_column h hh j

/-- All 41 columns with a proved density interpretation, using one common
representative for each arbitrary seven-vertex graph. -/
theorem density_columns_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows, Nonempty (BooleanGraphEquiv g (maskGraph 7 h.mask)) ∧
      (∀ i : Fin 3, ((freeColumns Generated.certificate h)[i.val]! : ℚ) / 557383680 =
        (semanticFreePrimitiveColumns g)[i.val]!) ∧
      (∀ i : Fin 4, ((positiveColumns Generated.certificate h)[i.val]! : ℚ) / 557383680 =
        (semanticPositiveColumns g)[i.val]!) ∧
      (∀ j : Fin 34, ((freeColumns Generated.certificate h)[j.val + 3]! : ℚ) / 557383680 =
        semanticFixedColumn g j) ∧
      hostLeft Generated.certificate h = hostRight Generated.certificate Generated.gramData h := by
  obtain ⟨h, hh, ⟨e⟩, _⟩ := primitive_counts_on_all_seven_vertex_graphs g
  refine ⟨h, hh, ⟨e⟩, ?_, ?_, ?_, certificate_host_identities h hh⟩
  · intro i
    rw [semanticFreePrimitiveColumns_isomorphic e]
    exact freePrimitiveColumns_certificate h hh i
  · intro i
    rw [semanticPositiveColumns_isomorphic e]
    exact positiveColumns_certificate h hh i
  · intro j
    rw [semanticFixedColumn_isomorphic e]
    exact fixedColumn_certificate h hh j

end InducedPentagons.Paper



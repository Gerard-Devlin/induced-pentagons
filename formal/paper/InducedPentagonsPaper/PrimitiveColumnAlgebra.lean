import InducedPentagonsPaper.FixedColumnAlgebra
import InducedPentagonsPaper.PrimitiveCertificate

/-! Exact rational normalization of the primitive columns in the integer
certificate, and their interpretation by injective pattern sampling. -/

namespace InducedPentagons.Paper

theorem certificate_pattern_denominators :
    Generated.certificate.patternDenominators = expectedPatternDenominators := by
  decide +kernel

/-- The normalized primitive count stored in a certificate row. -/
def rowPrimitiveDensity (h : HostRow) (i : Nat) : ℚ :=
  (h.primitive[i]! : ℚ) / (expectedPatternDenominators[i]! : ℚ)

theorem primitive_free_column0 (h : HostRow) :
    ((freeColumns Generated.certificate h)[0]! : ℚ) / 557383680 =
      (5 / 144 : ℚ) * rowPrimitiveDensity h 2 -
      (5 / 663552 : ℚ) * rowPrimitiveDensity h 5 := by
  norm_num [freeColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_free_column1 (h : HostRow) :
    ((freeColumns Generated.certificate h)[1]! : ℚ) / 557383680 =
      (5 / 144 : ℚ) * rowPrimitiveDensity h 3 -
      (5 / 663552 : ℚ) * rowPrimitiveDensity h 6 := by
  norm_num [freeColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_free_column2 (h : HostRow) :
    ((freeColumns Generated.certificate h)[2]! : ℚ) / 557383680 =
      (5 / 144 : ℚ) * rowPrimitiveDensity h 4 -
      (5 / 663552 : ℚ) * rowPrimitiveDensity h 7 := by
  norm_num [freeColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_positive_column0 (h : HostRow) :
    ((positiveColumns Generated.certificate h)[0]! : ℚ) / 557383680 =
      (5 / 144 : ℚ) * rowPrimitiveDensity h 8 -
      (5 / 663552 : ℚ) * rowPrimitiveDensity h 9 := by
  norm_num [positiveColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_positive_column1 (h : HostRow) :
    ((positiveColumns Generated.certificate h)[1]! : ℚ) / 557383680 =
      rowPrimitiveDensity h 11 - rowPrimitiveDensity h 12 -
      (1 / 9216 : ℚ) * rowPrimitiveDensity h 10 := by
  norm_num [positiveColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_positive_column2 (h : HostRow) :
    ((positiveColumns Generated.certificate h)[2]! : ℚ) / 557383680 =
      rowPrimitiveDensity h 14 - rowPrimitiveDensity h 15 -
      (1 / 9216 : ℚ) * rowPrimitiveDensity h 13 := by
  norm_num [positiveColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_positive_column3 (h : HostRow) :
    ((positiveColumns Generated.certificate h)[3]! : ℚ) / 557383680 =
      (1 / 2 : ℚ) * rowPrimitiveDensity h 16 -
      (1 / 9216 : ℚ) * rowPrimitiveDensity h 21 -
      (1 / 2 : ℚ) * (rowPrimitiveDensity h 17 + rowPrimitiveDensity h 18 +
        rowPrimitiveDensity h 19 + rowPrimitiveDensity h 20) := by
  norm_num [positiveColumns, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity, intSum,
    List.range_succ, List.foldl]
  ring

theorem primitive_hostLeft_normalized (h : HostRow) :
    (hostLeft Generated.certificate h : ℚ) / 557383680 =
      ((5 / 663552 : ℚ) - rowPrimitiveDensity h 1) *
        (Generated.certificate.scale : ℚ) := by
  norm_num [hostLeft, patternTerm, certificate_data_denominator,
    certificate_pattern_denominators, expectedPatternDenominators, rowPrimitiveDensity]
  ring

theorem primitive_certificate_density_entry (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (i : Fin 22) :
    (primitiveSemanticDensities primitivePatternSpecs (maskGraph 7 h.mask))[i.val]! =
      rowPrimitiveDensity h i.val := by
  rw [primitive_certificate_densities h hh]
  unfold rowPrimitiveDensity
  have hi : i.val < h.primitive.size := by rw [primitive_certificate_row_width h hh]; exact i.isLt
  have hd : i.val < expectedPatternDenominators.size := by
    change i.val < 22
    exact i.isLt
  rw [getElem!_pos _ _ (by simpa only [List.length_zipWith, Array.length_toList, lt_min_iff] using And.intro hi hd),
    getElem!_pos h.primitive i.val hi, getElem!_pos expectedPatternDenominators i.val hd]
  simp only [List.getElem_zipWith, Array.getElem_toList]

end InducedPentagons.Paper


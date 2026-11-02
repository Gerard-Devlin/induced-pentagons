import InducedPentagonsPaper.FixedDensityNormalization

/-! Exact scaling of the 34 fixed-density columns in the arithmetic certificate. -/

namespace InducedPentagons.Paper

theorem freeColumns_fixedAt (c : Certificate) (h : HostRow) (j : Fin 34) :
    (freeColumns c h)[j.val + 3]! =
      (144 * Int.ofNat h.complement[j.val]! - 5 * Int.ofNat h.induced[j.val]!) *
        (c.dataDenominator / 3024 : Nat) := by
  have hj := j.isLt
  unfold freeColumns
  rw [getElem!_pos _ _ (by simp; omega)]
  rw [Array.getElem_append_right (by simp)]
  simp

theorem fixedColumn_scale (a b : Nat) :
    (((144 * (a : Int) - 5 * (b : Int)) * (557383680 / 3024 : Nat) : Int) : ℚ) / 557383680 =
      (a : ℚ) / 21 - (5 / 144 : ℚ) * (b : ℚ) / 21 := by
  push_cast
  norm_num
  ring

theorem certificate_data_denominator : Generated.certificate.dataDenominator = 557383680 := by
  decide +kernel

theorem freeColumns_fixed_normalized (h : HostRow) (j : Fin 34) :
    ((freeColumns Generated.certificate h)[j.val + 3]! : ℚ) /
        (Generated.certificate.dataDenominator : ℚ) =
      (h.complement[j.val]! : ℚ) / 21 - (5 / 144 : ℚ) * (h.induced[j.val]! : ℚ) / 21 := by
  rw [freeColumns_fixedAt, certificate_data_denominator]
  exact fixedColumn_scale _ _

end InducedPentagons.Paper

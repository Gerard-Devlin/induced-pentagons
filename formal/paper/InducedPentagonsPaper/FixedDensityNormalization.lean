import InducedPentagonsPaper.FixedDensityIsomorphism

/-! The 34 graph types partition the five-subsets, giving probability densities. -/

open scoped BigOperators

namespace InducedPentagons.Paper

def fiveSubsetClass {n : Nat} (g : Graph (Fin n)) (s : Finset (Fin n)) : Nat :=
  if hs : s.card = 5 then fiveGraphType (subsetGraph g s hs) else 0

theorem fixedDensityCounts_sum {n : Nat} (g : Graph (Fin n)) :
    (fixedDensityCounts g).sum = n.choose 5 := by
  let samples : Finset (Finset (Fin n)) := Finset.univ.powersetCard 5
  have hm : (samples : Set (Finset (Fin n))).MapsTo (fiveSubsetClass g) fixedTypeMasks.toFinset := by
    intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    simpa [fiveSubsetClass, hc] using (fiveGraphType_sound (subsetGraph g s hc)).1
  have heach (m : Nat) : fixedDensityCount g m =
      (samples.filter (fun s => fiveSubsetClass g s = m)).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    simp [fixedSubsetCheck, fiveSubsetClass, hc]
  change (fixedTypeMasks.map (fixedDensityCount g)).sum = n.choose 5
  rw [← List.sum_toFinset (fixedDensityCount g) fixed_type_masks_nodup]
  simp_rw [heach]
  simpa [samples, Finset.card_powersetCard] using (Finset.card_eq_sum_card_fiberwise hm).symm

def fiveTypeDensity {n : Nat} (g : Graph (Fin n)) (m : Nat) : ℚ :=
  (fixedDensityCount g m : ℚ) / (n.choose 5 : ℚ)

def fiveTypeComplementDensity {n : Nat} (g : Graph (Fin n)) (m : Nat) : ℚ :=
  (fixedComplementCount g m : ℚ) / (n.choose 5 : ℚ)

theorem fiveTypeDensity_nonnegative {n : Nat} (g : Graph (Fin n)) (m : Nat) :
    0 ≤ fiveTypeDensity g m := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem fiveTypeComplementDensity_nonnegative {n : Nat} (g : Graph (Fin n)) (m : Nat) :
    0 ≤ fiveTypeComplementDensity g m := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem fiveTypeDensity_le_one {n : Nat} (g : Graph (Fin n)) (m : Nat) :
    fiveTypeDensity g m ≤ 1 := by
  unfold fiveTypeDensity
  by_cases hz : n.choose 5 = 0
  · simp [hz]
  · have hp : (0 : ℚ) < (n.choose 5 : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    apply (div_le_one hp).mpr
    exact_mod_cast fixedDensityCount_le g m

theorem fiveTypeComplementDensity_le {n : Nat} (g : Graph (Fin n)) (m : Nat) :
    fiveTypeComplementDensity g m ≤ fiveTypeDensity g m := by
  unfold fiveTypeComplementDensity fiveTypeDensity
  exact div_le_div_of_nonneg_right (by exact_mod_cast fixedComplementCount_le g m) (Nat.cast_nonneg _)

theorem fiveTypeDensities_sum {n : Nat} (g : Graph (Fin n)) (hn : 5 ≤ n) :
    (fixedTypeMasks.map (fiveTypeDensity g)).sum = 1 := by
  rw [← List.sum_toFinset (fiveTypeDensity g) fixed_type_masks_nodup]
  change (∑ m ∈ fixedTypeMasks.toFinset, (fixedDensityCount g m : ℚ) / (n.choose 5 : ℚ)) = 1
  rw [← Finset.sum_div]
  have hc : (∑ m ∈ fixedTypeMasks.toFinset, (fixedDensityCount g m : ℚ)) = (n.choose 5 : ℚ) := by
    exact_mod_cast (List.sum_toFinset (fixedDensityCount g) fixed_type_masks_nodup).trans
      (fixedDensityCounts_sum g)
  rw [hc]
  apply div_self
  exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hn)

end InducedPentagons.Paper

import InducedPentagonsPaper.ProfileMaskBound

namespace InducedPentagons.Paper

/-- Every fractional Clebsch profile has rooted pentagon link at most sixty. -/
theorem profileLink_le_sixty {x : Fin 16 → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    profileLink x ≤ 60 := by
  exact profileLink_le_sixty_from_masks hx

end InducedPentagons.Paper

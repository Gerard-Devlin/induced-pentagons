import InducedPentagonsPaper.ProfileMaskData
import InducedPentagonsPaper.Generated.ProfilePrefixComplete

namespace InducedPentagons.Paper

theorem profileLink_le_sixty_from_masks {x : Fin 16 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : profileLink x ≤ 60 := by
  rw [profileLink_mask_sum, ← bernoulliExtension_patternTotal]
  exact bernoulliExtension_le hx clebsch_profile_boolean_bound

end InducedPentagons.Paper

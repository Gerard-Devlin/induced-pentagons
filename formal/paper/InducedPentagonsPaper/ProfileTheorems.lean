import InducedPentagonsPaper.PathConvention
import InducedPentagonsPaper.ProfileEnvelope
import InducedPentagonsPaper.ProfileAttainment

namespace InducedPentagons.Paper

/-- Lemma 11.1 in the manuscript's induced-four-subset convention. -/
theorem profile_envelope_on_induced_subsets {x : Fin 16 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    setProfileLink clebsch x ≤ min ((12 / 5 : ℝ) * profileDegree x ^ 2) 60 := by
  rw [← profileLink_eq_setProfileLink]
  exact profile_envelope hx

theorem profile_envelope_attained_on_induced_subsets {d : ℝ}
    (hd : 0 ≤ d) (hd5 : d ≤ 5) (v : Fin 16) :
    (∀ i, 0 ≤ neighborhoodProfile v (d / 5) i ∧ neighborhoodProfile v (d / 5) i ≤ 1) ∧
    profileDegree (neighborhoodProfile v (d / 5)) = d ∧
    setProfileLink clebsch (neighborhoodProfile v (d / 5)) = (12 / 5 : ℝ) * d ^ 2 := by
  have h := profile_envelope_attained hd hd5 v
  rw [← profileLink_eq_setProfileLink]
  exact h

/-- Lemma 12.1 / equation (58), with c(p) summed over induced P4 vertex subsets. -/
theorem scalar_profile_on_induced_subsets (profiles : List (Fin 16 → ℝ))
    (hp : ∀ p ∈ profiles, ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ell : ℤ) :
    20 * (1 - a) * min (3 * a) 1 ≤
      (profiles.map (fun p => 12 * profileDegree p - setProfileLink clebsch p)).sum +
      max (12 * (5 * (a + ell) - (profiles.map profileDegree).sum))
        (-4 * (5 * (a + ell) - (profiles.map profileDegree).sum)) := by
  have h := scalar_profile_equation58 profiles hp ha ha1 ell
  simpa only [profileLink_eq_setProfileLink] using h

end InducedPentagons.Paper

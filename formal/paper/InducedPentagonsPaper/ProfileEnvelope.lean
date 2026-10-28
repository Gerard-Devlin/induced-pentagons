import InducedPentagonsPaper.ProfileBound
import InducedPentagonsPaper.ProfileQuadratic
import InducedPentagonsPaper.ScalarProfile

namespace InducedPentagons.Paper

theorem profileDegree_nonnegative {x : Fin 16 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ profileDegree x := Finset.sum_nonneg (fun i _ => hx i)

/-- Both upper bounds in the profile envelope, for the graph-defined canonical
induced-path model. The attainment part is a separate statement. -/
theorem profile_envelope {x : Fin 16 → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    profileLink x ≤ min ((12 / 5 : ℝ) * profileDegree x ^ 2) 60 :=
  le_min (profileLink_le_quadratic hx) (profileLink_le_sixty hx)

/-- The scalar profile lemma with all Clebsch envelope hypotheses discharged. -/
theorem scalar_profile_clebsch (profiles : List (Fin 16 → ℝ))
    (hp : ∀ p ∈ profiles, ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ell : ℤ) :
    phaseCost a ≤ (profiles.map (fun p => 12 * profileDegree p - profileLink p)).sum +
      phasePenalty (a + ell - (profiles.map (fun p => profileDegree p / 5)).sum) := by
  have he : ∀ q ∈ profiles.map (fun p => (profileDegree p, profileLink p)),
      0 ≤ q.1 ∧ q.2 ≤ (12 / 5 : ℝ) * q.1 ^ 2 ∧ q.2 ≤ 60 := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨p, hpm, rfl⟩
    exact ⟨profileDegree_nonnegative (fun i => (hp p hpm i).1),
      profileLink_le_quadratic (hp p hpm), profileLink_le_sixty (hp p hpm)⟩
  simpa only [List.map_map, Function.comp_def] using scalar_profile _ he ha ha1 ell

/-- Equation (58), with its adjustment term written exactly as max(12u,-4u). -/
theorem scalar_profile_equation58 (profiles : List (Fin 16 → ℝ))
    (hp : ∀ p ∈ profiles, ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ell : ℤ) :
    20 * (1 - a) * min (3 * a) 1 ≤
      (profiles.map (fun p => 12 * profileDegree p - profileLink p)).sum +
      max (12 * (5 * (a + ell) - (profiles.map profileDegree).sum))
        (-4 * (5 * (a + ell) - (profiles.map profileDegree).sum)) := by
  have h := scalar_profile_clebsch profiles hp ha ha1 ell
  have hs : (profiles.map (fun p => profileDegree p / 5)).sum =
      (profiles.map profileDegree).sum / 5 := by
    simp only [div_eq_mul_inv, List.sum_map_mul_right]
  have he : phasePenalty (a + ell - (profiles.map (fun p => profileDegree p / 5)).sum) =
      max (12 * (5 * (a + ell) - (profiles.map profileDegree).sum))
        (-4 * (5 * (a + ell) - (profiles.map profileDegree).sum)) := by
    rw [hs]
    unfold phasePenalty
    congr 1 <;> ring
  rw [he] at h
  exact h

end InducedPentagons.Paper

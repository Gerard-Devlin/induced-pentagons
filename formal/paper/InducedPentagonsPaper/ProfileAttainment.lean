import InducedPentagonsPaper.ProfileQuadratic

namespace InducedPentagons.Paper

noncomputable def neighborhoodProfile (v : Fin 16) (t : ℝ) (i : Fin 16) : ℝ :=
  if clebsch.adj v i then t else 0

theorem neighborhoodProfile_range (v : Fin 16) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ i, 0 ≤ neighborhoodProfile v t i ∧ neighborhoodProfile v t i ≤ 1 := by
  intro i
  unfold neighborhoodProfile
  split_ifs <;> constructor <;> linarith

theorem neighborhoodProfile_degree (v : Fin 16) (t : ℝ) :
    profileDegree (neighborhoodProfile v t) = 5 * t := by
  unfold profileDegree neighborhoodProfile
  rw [← sum_finRange]
  rw [← list_sum_filter_map]
  change ((neighbors clebsch v).map (fun _ => t)).sum = _
  simp [List.map_const', clebsch_degree] <;> ring

theorem pathValue_neighborhood {p : PathTuple 16} (hp : p ∈ inducedPaths clebsch)
    (v : Fin 16) (t : ℝ) :
    patternValue (pathLiteral p) (neighborhoodProfile v t) =
      if clebsch.adj v p.a && clebsch.adj v p.d then t ^ 2 else 0 := by
  have ha : pathLiteral p p.a = some true := by simp [pathLiteral]
  have hd : pathLiteral p p.d = some true := by simp [pathLiteral]
  have hne : p.a ≠ p.d := ne_of_lt ((mem_inducedPaths clebsch p).mp hp).1
  have hpath := ((mem_inducedPaths clebsch p).mp hp).2
  by_cases hA : clebsch.adj v p.a = true
  · by_cases hD : clebsch.adj v p.d = true
    · have hB : clebsch.adj v p.b = false := clebsch_triangle_free v p.a p.b hA hpath.2.1
      have hC : clebsch.adj v p.c = false := by
        apply clebsch_triangle_free v p.d p.c hD
        rw [clebsch.symmetric]
        exact hpath.2.2.2.1
      let f : Fin 16 → ℝ := fun i => match pathLiteral p i with
        | none => 1
        | some true => neighborhoodProfile v t i
        | some false => 1 - neighborhoodProfile v t i
      have hfa : f p.a = t := by simp [f, ha, neighborhoodProfile, hA]
      have hfd : f p.d = t := by simp [f, hd, neighborhoodProfile, hD]
      have hf : ∀ i, i ∉ ({p.a, p.d} : Finset (Fin 16)) → f i = 1 := by
        intro i hi
        have hi' : i ≠ p.a ∧ i ≠ p.d := by simpa using hi
        by_cases hb : i = p.b
        · subst i
          simp [f, pathLiteral, hi'.1, hi'.2, neighborhoodProfile, hB]
        · by_cases hc : i = p.c
          · subst i
            simp [f, pathLiteral, hi'.1, hi'.2, neighborhoodProfile, hC]
          · simp [f, pathLiteral, hi'.1, hi'.2, hb, hc]
      have hprod : (∏ i, f i) = ∏ i ∈ ({p.a, p.d} : Finset (Fin 16)), f i :=
        (Finset.prod_subset (by simp) (fun i _ hi => hf i hi)).symm
      change (∏ i, f i) = _
      rw [hprod, Finset.prod_pair hne, hfa, hfd]
      simp [hA, hD, pow_two]
    · have hz : neighborhoodProfile v t p.d = 0 := by simp [neighborhoodProfile, hD]
      have hzero : patternValue (pathLiteral p) (neighborhoodProfile v t) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ p.d)
        simp [hd, hz]
      simp [hzero, hD]
  · have hz : neighborhoodProfile v t p.a = 0 := by simp [neighborhoodProfile, hA]
    have hzero : patternValue (pathLiteral p) (neighborhoodProfile v t) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p.a)
      simp [ha, hz]
    simp [hzero, hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clebsch_neighborhood_path_count : ∀ v : Fin 16,
    ((inducedPaths clebsch).filter (fun p => clebsch.adj v p.a && clebsch.adj v p.d)).length = 60 := by
  decide +kernel

theorem neighborhoodProfile_link (v : Fin 16) (t : ℝ) :
    profileLink (neighborhoodProfile v t) = 60 * t ^ 2 := by
  unfold profileLink
  have hmap : (inducedPaths clebsch).map
      (fun p => patternValue (pathLiteral p) (neighborhoodProfile v t)) =
      (inducedPaths clebsch).map
        (fun p => if clebsch.adj v p.a && clebsch.adj v p.d then t ^ 2 else 0) := by
    apply List.map_congr_left
    intro p hp
    exact pathValue_neighborhood hp v t
  rw [hmap, ← list_sum_filter_map]
  simp [List.map_const', clebsch_neighborhood_path_count] <;> ring

theorem profile_envelope_attained {d : ℝ} (hd : 0 ≤ d) (hd5 : d ≤ 5) (v : Fin 16) :
    (∀ i, 0 ≤ neighborhoodProfile v (d / 5) i ∧ neighborhoodProfile v (d / 5) i ≤ 1) ∧
    profileDegree (neighborhoodProfile v (d / 5)) = d ∧
    profileLink (neighborhoodProfile v (d / 5)) = (12 / 5 : ℝ) * d ^ 2 := by
  refine ⟨neighborhoodProfile_range v (by linarith) (by linarith), ?_, ?_⟩
  · rw [neighborhoodProfile_degree]; ring
  · rw [neighborhoodProfile_link]; ring

end InducedPentagons.Paper

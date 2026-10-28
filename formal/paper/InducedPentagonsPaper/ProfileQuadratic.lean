import InducedPentagonsPaper.ProfileData
import InducedPentagonsPaper.ClebschComplement
import InducedPentagonsPaper.OrderedEdgeSum

namespace InducedPentagons.Paper

theorem pathValue_le_endpoints {n : Nat} (p : PathTuple n)
    (hne : p.a ≠ p.d) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    patternValue (pathLiteral p) x ≤ x p.a * x p.d := by
  let f : Fin n → ℝ := fun i => match pathLiteral p i with
    | none => 1
    | some true => x i
    | some false => 1 - x i
  have hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i
    dsimp only [f]
    cases pathLiteral p i with
    | none => norm_num
    | some b => cases b <;> simp only <;> constructor <;> linarith [(hx i).1, (hx i).2]
  have ha : f p.a = x p.a := by simp [f, pathLiteral]
  have hd : f p.d = x p.d := by simp [f, pathLiteral]
  have h := Finset.prod_le_prod_of_subset_of_le_one₀
    (s := {p.a, p.d}) (t := Finset.univ) (f := f) (by simp)
    (fun i _ => (hf i).1) (fun i _ _ => (hf i).2)
  change (∏ i, f i) ≤ x p.a * x p.d
  simpa only [Finset.prod_pair hne, ha, hd] using h

theorem profileLink_le_endpointSum {x : Fin 16 → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    profileLink x ≤ ((inducedPaths clebsch).map (fun p => x p.a * x p.d)).sum := by
  unfold profileLink
  apply List.sum_le_sum
  intro p hp
  exact pathValue_le_endpoints p (ne_of_lt ((mem_inducedPaths clebsch p).mp hp).1) hx

def nonedgePairs {n : Nat} (g : Graph (Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter (fun v => decide (u < v) && !(g.adj u v))).map (u, ·)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Each nonadjacent Clebsch endpoint pair occurs exactly six times. -/
theorem clebsch_path_endpoint_multiplicity :
    ((inducedPaths clebsch).map (fun p => (p.a, p.d))).Perm
      ((nonedgePairs clebsch).flatMap (fun p => List.replicate 6 p)) := by
  decide +kernel

theorem nonedgePairs_weight_sum {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) :
    ((nonedgePairs g).map (fun p => x p.1 * x p.2)).sum =
      edgeMass (graphComplement g) x := by
  rw [edgeMass_eq_orderedEdgeSum]
  unfold nonedgePairs orderedEdgeSum
  rw [List.map_flatMap, list_sum_flatMap]
  simp_rw [List.map_map]
  rw [sum_finRange]
  apply Finset.sum_congr rfl
  intro u _
  rw [list_sum_filter_map, sum_finRange]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : u < v
  · cases hadj : g.adj u v <;> simp [h, hadj, graphComplement, ne_of_lt h]
  · simp [h]

theorem clebsch_endpoint_weight_sum (x : Fin 16 → ℝ) :
    ((inducedPaths clebsch).map (fun p => x p.a * x p.d)).sum =
      6 * ((nonedgePairs clebsch).map (fun p => x p.1 * x p.2)).sum := by
  have h := (clebsch_path_endpoint_multiplicity.map (fun p => x p.1 * x p.2)).sum_eq
  simp only [List.map_map, Function.comp_def, List.map_flatMap, List.map_replicate,
    list_sum_flatMap, List.sum_replicate, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [h, List.sum_map_mul_left]

theorem profileLink_le_quadratic {x : Fin 16 → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    profileLink x ≤ (12 / 5 : ℝ) * profileDegree x ^ 2 := by
  apply (profileLink_le_endpointSum hx).trans
  rw [clebsch_endpoint_weight_sum, nonedgePairs_weight_sum]
  exact clebsch_complement_weighted (fun i => (hx i).1)

end InducedPentagons.Paper

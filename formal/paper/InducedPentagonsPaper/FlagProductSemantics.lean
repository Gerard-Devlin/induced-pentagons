import InducedPentagonsPaper.JointFlagGraphs

/-! Finite flag-product counts with rooted-isomorphism semantics for all five certificate bases.
These definitions do not yet certify the saved HostRow tensor entries. -/

namespace InducedPentagons.Paper

noncomputable def flagProductCount_one_root (g : Graph (Fin 7)) (i j : Fin 20) : Nat :=
  jointFlagPairCount (n := 7) (roots := 1) (free := 3) (by decide)
    (jointRootCheck (free := 3) 0 g) (fun x => indexedFlag_one_root (x.graph g)) i j

theorem flagProductCount_one_root_semantics (g : Graph (Fin 7)) (i j : Fin 20) :
    flagProductCount_one_root g i j =
      Nat.card {x : JointFlagSample 7 1 3 //
        JointFlagPairHasTypes (by decide) 0 indexedFlagBasis_one_root g i j x} :=
  jointFlagPairCount_semantics (n := 7) (roots := 1) (free := 3) (by decide) 0 indexedFlagBasis_one_root
    indexedFlag_one_root indexedFlag_one_root_eq_iff g i j

theorem flagProductCount_one_root_symmetric (g : Graph (Fin 7)) (i j : Fin 20) :
    flagProductCount_one_root g i j = flagProductCount_one_root g j i :=
  jointFlagPairCount_symmetric (by decide) _ _ i j

theorem flagProductCount_one_root_le (g : Graph (Fin 7)) (i j : Fin 20) :
    flagProductCount_one_root g i j ≤ 140 := by
  calc
    _ ≤ (7 : Nat).descFactorial 1 * (7 - 1).choose 3 := jointFlagPairCount_le (by decide) _ _ i j
    _ = 140 := by decide +kernel

theorem flagProductDenominator_one_root :
    (Generated.certificate.blocks[0]!).denominator =
      Fintype.card (JointFlagSample 7 1 3) := by
  rw [jointFlagSample_one_root_card]
  decide +kernel

noncomputable def flagProductCount_independent3 (g : Graph (Fin 7)) (i j : Fin 72) : Nat :=
  jointFlagPairCount (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 0 g) (fun x => indexedFlag_independent3 (x.graph g)) i j

theorem flagProductCount_independent3_semantics (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_independent3 g i j =
      Nat.card {x : JointFlagSample 7 3 2 //
        JointFlagPairHasTypes (by decide) 0 indexedFlagBasis_independent3 g i j x} :=
  jointFlagPairCount_semantics (n := 7) (roots := 3) (free := 2) (by decide) 0 indexedFlagBasis_independent3
    indexedFlag_independent3 indexedFlag_independent3_eq_iff g i j

theorem flagProductCount_independent3_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_independent3 g i j = flagProductCount_independent3 g j i :=
  jointFlagPairCount_symmetric (by decide) _ _ i j

theorem flagProductCount_independent3_le (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_independent3 g i j ≤ 1260 := by
  calc
    _ ≤ (7 : Nat).descFactorial 3 * (7 - 3).choose 2 := jointFlagPairCount_le (by decide) _ _ i j
    _ = 1260 := by decide +kernel

theorem flagProductDenominator_independent3 :
    (Generated.certificate.blocks[1]!).denominator =
      Fintype.card (JointFlagSample 7 3 2) := by
  rw [jointFlagSample_three_roots_card]
  decide +kernel

noncomputable def flagProductCount_edge_isolate (g : Graph (Fin 7)) (i j : Fin 72) : Nat :=
  jointFlagPairCount (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 1 g) (fun x => indexedFlag_edge_isolate (x.graph g)) i j

theorem flagProductCount_edge_isolate_semantics (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_edge_isolate g i j =
      Nat.card {x : JointFlagSample 7 3 2 //
        JointFlagPairHasTypes (by decide) 1 indexedFlagBasis_edge_isolate g i j x} :=
  jointFlagPairCount_semantics (n := 7) (roots := 3) (free := 2) (by decide) 1 indexedFlagBasis_edge_isolate
    indexedFlag_edge_isolate indexedFlag_edge_isolate_eq_iff g i j

theorem flagProductCount_edge_isolate_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_edge_isolate g i j = flagProductCount_edge_isolate g j i :=
  jointFlagPairCount_symmetric (by decide) _ _ i j

theorem flagProductCount_edge_isolate_le (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_edge_isolate g i j ≤ 1260 := by
  calc
    _ ≤ (7 : Nat).descFactorial 3 * (7 - 3).choose 2 := jointFlagPairCount_le (by decide) _ _ i j
    _ = 1260 := by decide +kernel

theorem flagProductDenominator_edge_isolate :
    (Generated.certificate.blocks[2]!).denominator =
      Fintype.card (JointFlagSample 7 3 2) := by
  rw [jointFlagSample_three_roots_card]
  decide +kernel

noncomputable def flagProductCount_path3 (g : Graph (Fin 7)) (i j : Fin 72) : Nat :=
  jointFlagPairCount (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 17 g) (fun x => indexedFlag_path3 (x.graph g)) i j

theorem flagProductCount_path3_semantics (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_path3 g i j =
      Nat.card {x : JointFlagSample 7 3 2 //
        JointFlagPairHasTypes (by decide) 17 indexedFlagBasis_path3 g i j x} :=
  jointFlagPairCount_semantics (n := 7) (roots := 3) (free := 2) (by decide) 17 indexedFlagBasis_path3
    indexedFlag_path3 indexedFlag_path3_eq_iff g i j

theorem flagProductCount_path3_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_path3 g i j = flagProductCount_path3 g j i :=
  jointFlagPairCount_symmetric (by decide) _ _ i j

theorem flagProductCount_path3_le (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_path3 g i j ≤ 1260 := by
  calc
    _ ≤ (7 : Nat).descFactorial 3 * (7 - 3).choose 2 := jointFlagPairCount_le (by decide) _ _ i j
    _ = 1260 := by decide +kernel

theorem flagProductDenominator_path3 :
    (Generated.certificate.blocks[3]!).denominator =
      Fintype.card (JointFlagSample 7 3 2) := by
  rw [jointFlagSample_three_roots_card]
  decide +kernel

noncomputable def flagProductCount_triangle3 (g : Graph (Fin 7)) (i j : Fin 72) : Nat :=
  jointFlagPairCount (n := 7) (roots := 3) (free := 2) (by decide)
    (jointRootCheck (free := 2) 19 g) (fun x => indexedFlag_triangle3 (x.graph g)) i j

theorem flagProductCount_triangle3_semantics (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_triangle3 g i j =
      Nat.card {x : JointFlagSample 7 3 2 //
        JointFlagPairHasTypes (by decide) 19 indexedFlagBasis_triangle3 g i j x} :=
  jointFlagPairCount_semantics (n := 7) (roots := 3) (free := 2) (by decide) 19 indexedFlagBasis_triangle3
    indexedFlag_triangle3 indexedFlag_triangle3_eq_iff g i j

theorem flagProductCount_triangle3_symmetric (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_triangle3 g i j = flagProductCount_triangle3 g j i :=
  jointFlagPairCount_symmetric (by decide) _ _ i j

theorem flagProductCount_triangle3_le (g : Graph (Fin 7)) (i j : Fin 72) :
    flagProductCount_triangle3 g i j ≤ 1260 := by
  calc
    _ ≤ (7 : Nat).descFactorial 3 * (7 - 3).choose 2 := jointFlagPairCount_le (by decide) _ _ i j
    _ = 1260 := by decide +kernel

theorem flagProductDenominator_triangle3 :
    (Generated.certificate.blocks[4]!).denominator =
      Fintype.card (JointFlagSample 7 3 2) := by
  rw [jointFlagSample_three_roots_card]
  decide +kernel

end InducedPentagons.Paper

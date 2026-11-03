import InducedPentagonsPaper.JointFlagIsomorphism
import InducedPentagonsPaper.FlagProductSemantics
import InducedPentagonsPaper.AtlasCertificate

/-! All five certificate flag-product counts are invariant under host isomorphism. -/

namespace InducedPentagons.Paper
theorem flagProductCount_one_root_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 20) :
    flagProductCount_one_root g i j = flagProductCount_one_root h i j :=
  jointFlagPairCount_isomorphic (n := 7) (m := 7) (roots := 1) (free := 3)
    (by decide) (by decide) 0 indexedFlagBasis_one_root indexedFlag_one_root
    indexedFlag_one_root_eq_iff e i j

theorem flagProductCount_independent3_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductCount_independent3 g i j = flagProductCount_independent3 h i j :=
  jointFlagPairCount_isomorphic (n := 7) (m := 7) (roots := 3) (free := 2)
    (by decide) (by decide) 0 indexedFlagBasis_independent3 indexedFlag_independent3
    indexedFlag_independent3_eq_iff e i j

theorem flagProductCount_edge_isolate_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductCount_edge_isolate g i j = flagProductCount_edge_isolate h i j :=
  jointFlagPairCount_isomorphic (n := 7) (m := 7) (roots := 3) (free := 2)
    (by decide) (by decide) 1 indexedFlagBasis_edge_isolate indexedFlag_edge_isolate
    indexedFlag_edge_isolate_eq_iff e i j

theorem flagProductCount_path3_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductCount_path3 g i j = flagProductCount_path3 h i j :=
  jointFlagPairCount_isomorphic (n := 7) (m := 7) (roots := 3) (free := 2)
    (by decide) (by decide) 17 indexedFlagBasis_path3 indexedFlag_path3
    indexedFlag_path3_eq_iff e i j

theorem flagProductCount_triangle3_isomorphic {g h : Graph (Fin 7)}
    (e : BooleanGraphEquiv g h) (i j : Fin 72) :
    flagProductCount_triangle3 g i j = flagProductCount_triangle3 h i j :=
  jointFlagPairCount_isomorphic (n := 7) (m := 7) (roots := 3) (free := 2)
    (by decide) (by decide) 19 indexedFlagBasis_triangle3 indexedFlag_triangle3
    indexedFlag_triangle3_eq_iff e i j
theorem flagProductCounts_reduced_to_certificate (g : Graph (Fin 7)) :
    ∃ m ∈ Generated.certificate.hosts.toList,
      (∀ i j, flagProductCount_one_root g i j =
        flagProductCount_one_root (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductCount_independent3 g i j =
        flagProductCount_independent3 (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductCount_edge_isolate g i j =
        flagProductCount_edge_isolate (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductCount_path3 g i j =
        flagProductCount_path3 (maskGraph 7 m) i j) ∧
      (∀ i j, flagProductCount_triangle3 g i j =
        flagProductCount_triangle3 (maskGraph 7 m) i j) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := atlas7_covers g
  refine ⟨m, ?_, flagProductCount_one_root_isomorphic e,
    flagProductCount_independent3_isomorphic e, flagProductCount_edge_isolate_isomorphic e,
    flagProductCount_path3_isomorphic e, flagProductCount_triangle3_isomorphic e⟩
  rwa [← atlas7_eq_certificate_hosts]

end InducedPentagons.Paper

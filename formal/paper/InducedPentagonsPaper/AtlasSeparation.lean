import InducedPentagonsPaper.Generated.HostCodeData

/-! Verified invariant count codes separate every pair of certificate hosts. -/

namespace InducedPentagons.Paper

theorem certificate_hosts_pairwise_nonisomorphic (a b : Nat)
    (ha : a ∈ Generated.certificate.hosts.toList) (hb : b ∈ Generated.certificate.hosts.toList)
    (e : toSimpleGraph (maskGraph 7 a) ≃g toSimpleGraph (maskGraph 7 b)) : a = b := by
  rw [← primitive_certificate_rows_masks] at ha hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
  have hmemr : (r.mask, rowCountCode r) ∈ rowCountPairs :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  have hmems : (s.mask, rowCountCode s) ∈ rowCountPairs :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  rw [storedHostCodes_binding] at hmemr hmems
  have hsig : rowCountCode r = rowCountCode s :=
    (rowCountCode_semantics r hr).trans
      ((graphCountCode_isomorphic (BooleanGraphEquiv.ofSimpleGraphIso e)).trans
        (rowCountCode_semantics s hs).symm)
  exact increasingHostCodes_separate sortedHostCodes_checked
    (r.mask, rowCountCode r) (storedHostCodes_permutation.mem_iff.mp hmemr)
    (s.mask, rowCountCode s) (storedHostCodes_permutation.mem_iff.mp hmems) hsig

theorem seven_vertex_graph_unique_certificate_host (g : Graph (Fin 7)) :
    ∃! m : Nat, m ∈ Generated.certificate.hosts.toList ∧
      Nonempty (toSimpleGraph g ≃g toSimpleGraph (maskGraph 7 m)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := seven_vertex_graph_isomorphic_to_certificate_host g
  refine ⟨m, ⟨hm, ⟨e⟩⟩, ?_⟩
  rintro b ⟨hb, ⟨f⟩⟩
  exact certificate_hosts_pairwise_nonisomorphic b m hb hm (f.symm.trans e)

theorem seven_vertex_simpleGraph_unique_certificate_host (g : SimpleGraph (Fin 7)) :
    ∃! m : Nat, m ∈ Generated.certificate.hosts.toList ∧
      Nonempty (g ≃g toSimpleGraph (maskGraph 7 m)) := by
  have h := seven_vertex_graph_unique_certificate_host (boolGraphOfSimpleGraph g)
  simpa only [toSimpleGraph_boolGraphOfSimpleGraph] using h

end InducedPentagons.Paper

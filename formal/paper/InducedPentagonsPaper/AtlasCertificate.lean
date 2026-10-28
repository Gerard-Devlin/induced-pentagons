import InducedPentagonsPaper.Generated.AtlasCoverage
import InducedPentagons.Generated.Inputs

/-! Connect the proved graph-atlas coverage to the certificate's actual host list. -/

namespace InducedPentagons.Paper

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem atlas7_eq_certificate_hosts : atlasMasks7 = Generated.certificate.hosts.toList := by
  decide +kernel

theorem seven_vertex_graph_isomorphic_to_certificate_host (g : Graph (Fin 7)) :
    ∃ m ∈ Generated.certificate.hosts.toList,
      Nonempty (toSimpleGraph g ≃g toSimpleGraph (maskGraph 7 m)) := by
  rw [← atlas7_eq_certificate_hosts]
  exact seven_vertex_graph_isomorphic_to_atlas g

theorem certificate_host_count : Generated.certificate.hosts.size = 1044 := by
  have h := atlas7_count
  rw [atlas7_eq_certificate_hosts, Array.length_toList] at h
  exact h

theorem edge5_eq_maskGraph (mask : Nat) (i j : Fin 5) :
    edge5 mask i.val j.val = if (maskGraph 5 mask).adj i j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem atlasWitnessCheck_rejects_noninjective :
    atlasWitnessCheck 1 0 0 ⟨0, 0⟩ = false := by decide +kernel

theorem atlasWitnessCheck_rejects_wrong_graph :
    atlasWitnessCheck 1 0 0 ⟨1, 8⟩ = false := by decide +kernel

theorem atlasRowCheck_rejects_missing_target :
    atlasRowCheck 0 [] ⟨0, fun _ => ⟨0, 0⟩⟩ = false := by decide +kernel

end InducedPentagons.Paper

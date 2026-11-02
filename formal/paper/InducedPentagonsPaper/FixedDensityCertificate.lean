import InducedPentagonsPaper.FixedDensityNormalization
import InducedPentagonsPaper.FixedColumnAlgebra
import InducedPentagonsPaper.Generated.FixedComplete
import InducedPentagonsPaper.PrimitiveCertificate

/-! Every saved fixed-density entry has induced-subset semantics, including its normalization. -/

namespace InducedPentagons.Paper

theorem fixed_certificate_induced_values (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.induced.toList = fixedDensityCounts (maskGraph 7 h.mask) :=
  congrArg Prod.fst (fixed_certificate_rows_semantics h hh)

theorem fixed_certificate_complement_values (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.complement.toList = fixedComplementCounts (maskGraph 7 h.mask) :=
  congrArg Prod.snd (fixed_certificate_rows_semantics h hh)

theorem fixed_certificate_induced_semantics (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.induced.toList = fixedTypeMasks.map
      (fun m => inducedTypeSetCount (maskGraph 5 m) (maskGraph 7 h.mask)) :=
  (congrArg Prod.fst (fixed_certificate_rows_semantics h hh)).trans
    (fixedDensityCounts_semantics (maskGraph 7 h.mask))

theorem fixed_certificate_complement_semantics (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.complement.toList = fixedTypeMasks.map
      (fun m => inducedTypeComplementCount (maskGraph 5 m) (maskGraph 7 h.mask)) :=
  (congrArg Prod.snd (fixed_certificate_rows_semantics h hh)).trans
    (fixedComplementCounts_semantics (maskGraph 7 h.mask))

theorem fixed_certificate_row_widths (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.induced.size = 34 ∧ h.complement.size = 34 := by
  have hi := congrArg List.length (congrArg Prod.fst (fixed_certificate_rows_semantics h hh))
  have hc := congrArg List.length (congrArg Prod.snd (fixed_certificate_rows_semantics h hh))
  constructor
  · simpa only [Array.length_toList, fixedDensityCounts, List.length_map, fixed_type_masks_count] using hi
  · simpa only [Array.length_toList, fixedComplementCounts, List.length_map, fixed_type_masks_count] using hc

theorem fixed_certificate_counts_sum (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    h.induced.toList.sum = 21 := by
  rw [fixed_certificate_induced_values h hh, fixedDensityCounts_sum]
  decide +kernel

theorem fixed_certificate_entry_values (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (j : Fin 34) :
    h.induced[j.val]! = fixedDensityCount (maskGraph 7 h.mask) fixedTypeMasks[j.val]! ∧
      h.complement[j.val]! = fixedComplementCount (maskGraph 7 h.mask) fixedTypeMasks[j.val]! := by
  have hj : j.val < fixedTypeMasks.length := by rw [fixed_type_masks_count]; exact j.isLt
  have hwidth := fixed_certificate_row_widths h hh
  have hib : j.val < h.induced.size := by rw [hwidth.1]; exact j.isLt
  have hcb : j.val < h.complement.size := by rw [hwidth.2]; exact j.isLt
  have hi := congrArg (fun l : List Nat => l[j.val]!)
    (congrArg Prod.fst (fixed_certificate_rows_semantics h hh))
  have hc := congrArg (fun l : List Nat => l[j.val]!)
    (congrArg Prod.snd (fixed_certificate_rows_semantics h hh))
  constructor
  · rw [getElem!_pos h.induced.toList j.val (by simpa using hib),
      getElem!_pos (fixedDensityCounts (maskGraph 7 h.mask)) j.val (by simpa [fixedDensityCounts] using hj)] at hi
    rw [getElem!_pos h.induced j.val hib, getElem!_pos fixedTypeMasks j.val hj]
    simpa only [fixedDensityCounts, List.getElem_map, Array.getElem_toList] using hi
  · rw [getElem!_pos h.complement.toList j.val (by simpa using hcb),
      getElem!_pos (fixedComplementCounts (maskGraph 7 h.mask)) j.val (by simpa [fixedComplementCounts] using hj)] at hc
    rw [getElem!_pos h.complement j.val hcb, getElem!_pos fixedTypeMasks j.val hj]
    simpa only [fixedComplementCounts, List.getElem_map, Array.getElem_toList] using hc

theorem fixed_certificate_free_column (h : HostRow) (hh : h ∈ primitiveCertificateRows)
    (j : Fin 34) :
    ((freeColumns Generated.certificate h)[j.val + 3]! : ℚ) /
        (Generated.certificate.dataDenominator : ℚ) =
      fiveTypeComplementDensity (maskGraph 7 h.mask) fixedTypeMasks[j.val]! -
        (5 / 144 : ℚ) * fiveTypeDensity (maskGraph 7 h.mask) fixedTypeMasks[j.val]! := by
  have hd : Nat.choose 7 5 = 21 := by decide +kernel
  rw [freeColumns_fixed_normalized, (fixed_certificate_entry_values h hh j).1,
    (fixed_certificate_entry_values h hh j).2]
  simp only [fiveTypeComplementDensity, fiveTypeDensity, hd]
  ring

theorem fixed_certificate_density_values (h : HostRow) (hh : h ∈ primitiveCertificateRows) :
    (fixedTypeMasks.map (fiveTypeDensity (maskGraph 7 h.mask)),
      fixedTypeMasks.map (fiveTypeComplementDensity (maskGraph 7 h.mask))) =
    (h.induced.toList.map (fun c : Nat => (c : ℚ) / 21),
      h.complement.toList.map (fun c : Nat => (c : ℚ) / 21)) := by
  have hd : Nat.choose 7 5 = 21 := by decide +kernel
  apply Prod.ext
  · dsimp only [Prod.fst]
    rw [fixed_certificate_induced_values h hh]
    simp only [fixedDensityCounts, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro m _
    norm_num [fiveTypeDensity, hd]
  · dsimp only [Prod.snd]
    rw [fixed_certificate_complement_values h hh]
    simp only [fixedComplementCounts, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro m _
    norm_num [fiveTypeComplementDensity, hd]

theorem fixed_counts_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows, Nonempty (BooleanGraphEquiv g (maskGraph 7 h.mask)) ∧
      (fixedDensityCounts g, fixedComplementCounts g) = (h.induced.toList, h.complement.toList) := by
  obtain ⟨h, hh, ⟨e⟩, _⟩ := primitive_counts_on_all_seven_vertex_graphs g
  refine ⟨h, hh, ⟨e⟩, ?_⟩
  rw [fixedDensityCounts_isomorphic e, fixedComplementCounts_isomorphic e]
  exact (fixed_certificate_rows_semantics h hh).symm

theorem fixed_semantic_counts_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows, Nonempty (BooleanGraphEquiv g (maskGraph 7 h.mask)) ∧
      (fixedTypeMasks.map (fun m => inducedTypeSetCount (maskGraph 5 m) g),
        fixedTypeMasks.map (fun m => inducedTypeComplementCount (maskGraph 5 m) g)) =
      (h.induced.toList, h.complement.toList) := by
  obtain ⟨h, hh, he, hc⟩ := fixed_counts_on_all_seven_vertex_graphs g
  refine ⟨h, hh, he, ?_⟩
  rw [← fixedDensityCounts_semantics, ← fixedComplementCounts_semantics]
  exact hc

theorem fixed_counts_on_all_seven_vertex_simpleGraphs (g : SimpleGraph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows, Nonempty (g ≃g toSimpleGraph (maskGraph 7 h.mask)) ∧
      (fixedDensityCounts (boolGraphOfSimpleGraph g), fixedComplementCounts (boolGraphOfSimpleGraph g)) =
      (h.induced.toList, h.complement.toList) := by
  obtain ⟨h, hh, ⟨e⟩, hc⟩ := fixed_counts_on_all_seven_vertex_graphs (boolGraphOfSimpleGraph g)
  refine ⟨h, hh, ?_, hc⟩
  have he := e.toSimpleGraphIso
  rw [toSimpleGraph_boolGraphOfSimpleGraph] at he
  exact ⟨he⟩

theorem fixed_changed_induced_count_rejected :
    ({ Generated.hostChunk000[0]! with induced :=
      #[20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] } : HostRow).induced.toList ≠
      fixedDensityCounts (maskGraph 7 0) := by
  have hv : fixedDensityCounts (maskGraph 7 0) =
      [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
    congrArg Prod.fst fixed_values_0000
  rw [hv]
  decide +kernel

theorem fixed_changed_complement_count_rejected :
    ({ Generated.hostChunk000[0]! with complement :=
      #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] } : HostRow).complement.toList ≠
      fixedComplementCounts (maskGraph 7 0) := by
  have hv : fixedComplementCounts (maskGraph 7 0) =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
    congrArg Prod.snd fixed_values_0000
  rw [hv]
  decide +kernel

end InducedPentagons.Paper

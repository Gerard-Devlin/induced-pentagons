import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData014
import InducedPentagonsPaper.Generated.FixedRows006

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0168 :
    (fixedDensityCounts (maskGraph 7 3055), fixedComplementCounts (maskGraph 7 3055)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 4, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0168_semantics :
    ((Generated.hostChunk014[0]).induced.toList, (Generated.hostChunk014[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[0]).mask)) := by
  have hm : (Generated.hostChunk014[0]).mask = 3055 := by decide +kernel
  have hv : ((Generated.hostChunk014[0]).induced.toList, (Generated.hostChunk014[0]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 4, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0168]

theorem fixed_values_0169 :
    (fixedDensityCounts (maskGraph 7 3064), fixedComplementCounts (maskGraph 7 3064)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 4, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0169_semantics :
    ((Generated.hostChunk014[1]).induced.toList, (Generated.hostChunk014[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[1]).mask)) := by
  have hm : (Generated.hostChunk014[1]).mask = 3064 := by decide +kernel
  have hv : ((Generated.hostChunk014[1]).induced.toList, (Generated.hostChunk014[1]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 4, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0169]

theorem fixed_values_0170 :
    (fixedDensityCounts (maskGraph 7 3065), fixedComplementCounts (maskGraph 7 3065)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0170_semantics :
    ((Generated.hostChunk014[2]).induced.toList, (Generated.hostChunk014[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[2]).mask)) := by
  have hm : (Generated.hostChunk014[2]).mask = 3065 := by decide +kernel
  have hv : ((Generated.hostChunk014[2]).induced.toList, (Generated.hostChunk014[2]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0170]

theorem fixed_values_0171 :
    (fixedDensityCounts (maskGraph 7 3066), fixedComplementCounts (maskGraph 7 3066)) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 2, 0, 3, 1, 0, 0, 2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0171_semantics :
    ((Generated.hostChunk014[3]).induced.toList, (Generated.hostChunk014[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[3]).mask)) := by
  have hm : (Generated.hostChunk014[3]).mask = 3066 := by decide +kernel
  have hv : ((Generated.hostChunk014[3]).induced.toList, (Generated.hostChunk014[3]).complement.toList) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 2, 0, 3, 1, 0, 0, 2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0171]

theorem fixed_values_0172 :
    (fixedDensityCounts (maskGraph 7 3067), fixedComplementCounts (maskGraph 7 3067)) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 2, 0, 3, 1, 0, 0, 0, 2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0172_semantics :
    ((Generated.hostChunk014[4]).induced.toList, (Generated.hostChunk014[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[4]).mask)) := by
  have hm : (Generated.hostChunk014[4]).mask = 3067 := by decide +kernel
  have hv : ((Generated.hostChunk014[4]).induced.toList, (Generated.hostChunk014[4]).complement.toList) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 2, 0, 3, 1, 0, 0, 0, 2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0172]

theorem fixed_values_0173 :
    (fixedDensityCounts (maskGraph 7 3070), fixedComplementCounts (maskGraph 7 3070)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0173_semantics :
    ((Generated.hostChunk014[5]).induced.toList, (Generated.hostChunk014[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[5]).mask)) := by
  have hm : (Generated.hostChunk014[5]).mask = 3070 := by decide +kernel
  have hv : ((Generated.hostChunk014[5]).induced.toList, (Generated.hostChunk014[5]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0173]

theorem fixed_values_0174 :
    (fixedDensityCounts (maskGraph 7 3071), fixedComplementCounts (maskGraph 7 3071)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 2, 2, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0174_semantics :
    ((Generated.hostChunk014[6]).induced.toList, (Generated.hostChunk014[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[6]).mask)) := by
  have hm : (Generated.hostChunk014[6]).mask = 3071 := by decide +kernel
  have hv : ((Generated.hostChunk014[6]).induced.toList, (Generated.hostChunk014[6]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 2, 2, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0174]

theorem fixed_values_0175 :
    (fixedDensityCounts (maskGraph 7 3896), fixedComplementCounts (maskGraph 7 3896)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 0, 9, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0175_semantics :
    ((Generated.hostChunk014[7]).induced.toList, (Generated.hostChunk014[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[7]).mask)) := by
  have hm : (Generated.hostChunk014[7]).mask = 3896 := by decide +kernel
  have hv : ((Generated.hostChunk014[7]).induced.toList, (Generated.hostChunk014[7]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 0, 9, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0175]

theorem fixed_values_0176 :
    (fixedDensityCounts (maskGraph 7 3897), fixedComplementCounts (maskGraph 7 3897)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0176_semantics :
    ((Generated.hostChunk014[8]).induced.toList, (Generated.hostChunk014[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[8]).mask)) := by
  have hm : (Generated.hostChunk014[8]).mask = 3897 := by decide +kernel
  have hv : ((Generated.hostChunk014[8]).induced.toList, (Generated.hostChunk014[8]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0176]

theorem fixed_values_0177 :
    (fixedDensityCounts (maskGraph 7 3898), fixedComplementCounts (maskGraph 7 3898)) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 0, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0177_semantics :
    ((Generated.hostChunk014[9]).induced.toList, (Generated.hostChunk014[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[9]).mask)) := by
  have hm : (Generated.hostChunk014[9]).mask = 3898 := by decide +kernel
  have hv : ((Generated.hostChunk014[9]).induced.toList, (Generated.hostChunk014[9]).complement.toList) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 0, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0177]

theorem fixed_values_0178 :
    (fixedDensityCounts (maskGraph 7 3899), fixedComplementCounts (maskGraph 7 3899)) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 0, 3, 3, 0, 0, 3, 0, 0, 0, 3, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0178_semantics :
    ((Generated.hostChunk014[10]).induced.toList, (Generated.hostChunk014[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[10]).mask)) := by
  have hm : (Generated.hostChunk014[10]).mask = 3899 := by decide +kernel
  have hv : ((Generated.hostChunk014[10]).induced.toList, (Generated.hostChunk014[10]).complement.toList) =
      ([0, 1, 0, 3, 1, 0, 0, 0, 0, 3, 3, 0, 0, 3, 0, 0, 0, 3, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0178]

theorem fixed_values_0179 :
    (fixedDensityCounts (maskGraph 7 3902), fixedComplementCounts (maskGraph 7 3902)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0179_semantics :
    ((Generated.hostChunk014[11]).induced.toList, (Generated.hostChunk014[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk014[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk014[11]).mask)) := by
  have hm : (Generated.hostChunk014[11]).mask = 3902 := by decide +kernel
  have hv : ((Generated.hostChunk014[11]).induced.toList, (Generated.hostChunk014[11]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0179]

theorem fixed_chunk_014_semantics :
    ∀ h ∈ Generated.hostChunk014.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk014.toList = [Generated.hostChunk014[0], Generated.hostChunk014[1], Generated.hostChunk014[2], Generated.hostChunk014[3], Generated.hostChunk014[4], Generated.hostChunk014[5], Generated.hostChunk014[6], Generated.hostChunk014[7], Generated.hostChunk014[8], Generated.hostChunk014[9], Generated.hostChunk014[10], Generated.hostChunk014[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0168_semantics
  · exact fixed_host_0169_semantics
  · exact fixed_host_0170_semantics
  · exact fixed_host_0171_semantics
  · exact fixed_host_0172_semantics
  · exact fixed_host_0173_semantics
  · exact fixed_host_0174_semantics
  · exact fixed_host_0175_semantics
  · exact fixed_host_0176_semantics
  · exact fixed_host_0177_semantics
  · exact fixed_host_0178_semantics
  · exact fixed_host_0179_semantics

end InducedPentagons.Paper

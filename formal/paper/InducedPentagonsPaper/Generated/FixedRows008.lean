import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData008
import InducedPentagonsPaper.Generated.FixedRows000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0096 :
    (fixedDensityCounts (maskGraph 7 2417), fixedComplementCounts (maskGraph 7 2417)) =
      ([0, 2, 4, 1, 0, 0, 2, 4, 0, 1, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0096_semantics :
    ((Generated.hostChunk008[0]).induced.toList, (Generated.hostChunk008[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[0]).mask)) := by
  have hm : (Generated.hostChunk008[0]).mask = 2417 := by decide +kernel
  have hv : ((Generated.hostChunk008[0]).induced.toList, (Generated.hostChunk008[0]).complement.toList) =
      ([0, 2, 4, 1, 0, 0, 2, 4, 0, 1, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0096]

theorem fixed_values_0097 :
    (fixedDensityCounts (maskGraph 7 2419), fixedComplementCounts (maskGraph 7 2419)) =
      ([0, 2, 3, 2, 0, 0, 0, 6, 0, 0, 2, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0097_semantics :
    ((Generated.hostChunk008[1]).induced.toList, (Generated.hostChunk008[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[1]).mask)) := by
  have hm : (Generated.hostChunk008[1]).mask = 2419 := by decide +kernel
  have hv : ((Generated.hostChunk008[1]).induced.toList, (Generated.hostChunk008[1]).complement.toList) =
      ([0, 2, 3, 2, 0, 0, 0, 6, 0, 0, 2, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0097]

theorem fixed_values_0098 :
    (fixedDensityCounts (maskGraph 7 2420), fixedComplementCounts (maskGraph 7 2420)) =
      ([0, 2, 3, 2, 0, 0, 0, 4, 0, 6, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0098_semantics :
    ((Generated.hostChunk008[2]).induced.toList, (Generated.hostChunk008[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[2]).mask)) := by
  have hm : (Generated.hostChunk008[2]).mask = 2420 := by decide +kernel
  have hv : ((Generated.hostChunk008[2]).induced.toList, (Generated.hostChunk008[2]).complement.toList) =
      ([0, 2, 3, 2, 0, 0, 0, 4, 0, 6, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0098]

theorem fixed_values_0099 :
    (fixedDensityCounts (maskGraph 7 2421), fixedComplementCounts (maskGraph 7 2421)) =
      ([0, 2, 3, 1, 1, 0, 0, 4, 0, 0, 7, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0099_semantics :
    ((Generated.hostChunk008[3]).induced.toList, (Generated.hostChunk008[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[3]).mask)) := by
  have hm : (Generated.hostChunk008[3]).mask = 2421 := by decide +kernel
  have hv : ((Generated.hostChunk008[3]).induced.toList, (Generated.hostChunk008[3]).complement.toList) =
      ([0, 2, 3, 1, 1, 0, 0, 4, 0, 0, 7, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0099]

theorem fixed_values_0100 :
    (fixedDensityCounts (maskGraph 7 2422), fixedComplementCounts (maskGraph 7 2422)) =
      ([0, 2, 2, 3, 0, 0, 0, 2, 2, 3, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0100_semantics :
    ((Generated.hostChunk008[4]).induced.toList, (Generated.hostChunk008[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[4]).mask)) := by
  have hm : (Generated.hostChunk008[4]).mask = 2422 := by decide +kernel
  have hv : ((Generated.hostChunk008[4]).induced.toList, (Generated.hostChunk008[4]).complement.toList) =
      ([0, 2, 2, 3, 0, 0, 0, 2, 2, 3, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0100]

theorem fixed_values_0101 :
    (fixedDensityCounts (maskGraph 7 2423), fixedComplementCounts (maskGraph 7 2423)) =
      ([0, 2, 2, 2, 1, 0, 0, 2, 2, 0, 3, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0101_semantics :
    ((Generated.hostChunk008[5]).induced.toList, (Generated.hostChunk008[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[5]).mask)) := by
  have hm : (Generated.hostChunk008[5]).mask = 2423 := by decide +kernel
  have hv : ((Generated.hostChunk008[5]).induced.toList, (Generated.hostChunk008[5]).complement.toList) =
      ([0, 2, 2, 2, 1, 0, 0, 2, 2, 0, 3, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0101]

theorem fixed_values_0102 :
    (fixedDensityCounts (maskGraph 7 2428), fixedComplementCounts (maskGraph 7 2428)) =
      ([0, 2, 2, 2, 1, 0, 0, 2, 0, 1, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0102_semantics :
    ((Generated.hostChunk008[6]).induced.toList, (Generated.hostChunk008[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[6]).mask)) := by
  have hm : (Generated.hostChunk008[6]).mask = 2428 := by decide +kernel
  have hv : ((Generated.hostChunk008[6]).induced.toList, (Generated.hostChunk008[6]).complement.toList) =
      ([0, 2, 2, 2, 1, 0, 0, 2, 0, 1, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0102]

theorem fixed_values_0103 :
    (fixedDensityCounts (maskGraph 7 2429), fixedComplementCounts (maskGraph 7 2429)) =
      ([0, 2, 2, 1, 2, 0, 0, 2, 0, 0, 4, 3, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 1, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0103_semantics :
    ((Generated.hostChunk008[7]).induced.toList, (Generated.hostChunk008[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[7]).mask)) := by
  have hm : (Generated.hostChunk008[7]).mask = 2429 := by decide +kernel
  have hv : ((Generated.hostChunk008[7]).induced.toList, (Generated.hostChunk008[7]).complement.toList) =
      ([0, 2, 2, 1, 2, 0, 0, 2, 0, 0, 4, 3, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 1, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0103]

theorem fixed_values_0104 :
    (fixedDensityCounts (maskGraph 7 2431), fixedComplementCounts (maskGraph 7 2431)) =
      ([0, 2, 2, 0, 3, 0, 0, 2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0104_semantics :
    ((Generated.hostChunk008[8]).induced.toList, (Generated.hostChunk008[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[8]).mask)) := by
  have hm : (Generated.hostChunk008[8]).mask = 2431 := by decide +kernel
  have hv : ((Generated.hostChunk008[8]).induced.toList, (Generated.hostChunk008[8]).complement.toList) =
      ([0, 2, 2, 0, 3, 0, 0, 2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0104]

theorem fixed_values_0105 :
    (fixedDensityCounts (maskGraph 7 2510), fixedComplementCounts (maskGraph 7 2510)) =
      ([0, 1, 7, 0, 0, 2, 0, 0, 4, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 5, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0105_semantics :
    ((Generated.hostChunk008[9]).induced.toList, (Generated.hostChunk008[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[9]).mask)) := by
  have hm : (Generated.hostChunk008[9]).mask = 2510 := by decide +kernel
  have hv : ((Generated.hostChunk008[9]).induced.toList, (Generated.hostChunk008[9]).complement.toList) =
      ([0, 1, 7, 0, 0, 2, 0, 0, 4, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 5, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0105]

theorem fixed_values_0106 :
    (fixedDensityCounts (maskGraph 7 2511), fixedComplementCounts (maskGraph 7 2511)) =
      ([0, 1, 4, 0, 0, 5, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0106_semantics :
    ((Generated.hostChunk008[10]).induced.toList, (Generated.hostChunk008[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[10]).mask)) := by
  have hm : (Generated.hostChunk008[10]).mask = 2511 := by decide +kernel
  have hv : ((Generated.hostChunk008[10]).induced.toList, (Generated.hostChunk008[10]).complement.toList) =
      ([0, 1, 4, 0, 0, 5, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0106]

theorem fixed_values_0107 :
    (fixedDensityCounts (maskGraph 7 2518), fixedComplementCounts (maskGraph 7 2518)) =
      ([0, 1, 4, 0, 0, 2, 1, 4, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0107_semantics :
    ((Generated.hostChunk008[11]).induced.toList, (Generated.hostChunk008[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk008[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk008[11]).mask)) := by
  have hm : (Generated.hostChunk008[11]).mask = 2518 := by decide +kernel
  have hv : ((Generated.hostChunk008[11]).induced.toList, (Generated.hostChunk008[11]).complement.toList) =
      ([0, 1, 4, 0, 0, 2, 1, 4, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0107]

theorem fixed_chunk_008_semantics :
    ∀ h ∈ Generated.hostChunk008.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk008.toList = [Generated.hostChunk008[0], Generated.hostChunk008[1], Generated.hostChunk008[2], Generated.hostChunk008[3], Generated.hostChunk008[4], Generated.hostChunk008[5], Generated.hostChunk008[6], Generated.hostChunk008[7], Generated.hostChunk008[8], Generated.hostChunk008[9], Generated.hostChunk008[10], Generated.hostChunk008[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0096_semantics
  · exact fixed_host_0097_semantics
  · exact fixed_host_0098_semantics
  · exact fixed_host_0099_semantics
  · exact fixed_host_0100_semantics
  · exact fixed_host_0101_semantics
  · exact fixed_host_0102_semantics
  · exact fixed_host_0103_semantics
  · exact fixed_host_0104_semantics
  · exact fixed_host_0105_semantics
  · exact fixed_host_0106_semantics
  · exact fixed_host_0107_semantics

end InducedPentagons.Paper

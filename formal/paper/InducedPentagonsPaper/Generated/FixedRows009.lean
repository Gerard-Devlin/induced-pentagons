import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData009
import InducedPentagonsPaper.Generated.FixedRows001

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0108 :
    (fixedDensityCounts (maskGraph 7 2519), fixedComplementCounts (maskGraph 7 2519)) =
      ([0, 1, 4, 0, 0, 2, 0, 1, 8, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0108_semantics :
    ((Generated.hostChunk009[0]).induced.toList, (Generated.hostChunk009[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[0]).mask)) := by
  have hm : (Generated.hostChunk009[0]).mask = 2519 := by decide +kernel
  have hv : ((Generated.hostChunk009[0]).induced.toList, (Generated.hostChunk009[0]).complement.toList) =
      ([0, 1, 4, 0, 0, 2, 0, 1, 8, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0108]

theorem fixed_values_0109 :
    (fixedDensityCounts (maskGraph 7 2520), fixedComplementCounts (maskGraph 7 2520)) =
      ([0, 1, 4, 0, 0, 2, 4, 3, 2, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0109_semantics :
    ((Generated.hostChunk009[1]).induced.toList, (Generated.hostChunk009[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[1]).mask)) := by
  have hm : (Generated.hostChunk009[1]).mask = 2520 := by decide +kernel
  have hv : ((Generated.hostChunk009[1]).induced.toList, (Generated.hostChunk009[1]).complement.toList) =
      ([0, 1, 4, 0, 0, 2, 4, 3, 2, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0109]

theorem fixed_values_0110 :
    (fixedDensityCounts (maskGraph 7 2521), fixedComplementCounts (maskGraph 7 2521)) =
      ([0, 1, 4, 0, 0, 1, 2, 2, 6, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0110_semantics :
    ((Generated.hostChunk009[2]).induced.toList, (Generated.hostChunk009[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[2]).mask)) := by
  have hm : (Generated.hostChunk009[2]).mask = 2521 := by decide +kernel
  have hv : ((Generated.hostChunk009[2]).induced.toList, (Generated.hostChunk009[2]).complement.toList) =
      ([0, 1, 4, 0, 0, 1, 2, 2, 6, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0110]

theorem fixed_values_0111 :
    (fixedDensityCounts (maskGraph 7 2522), fixedComplementCounts (maskGraph 7 2522)) =
      ([0, 1, 3, 1, 0, 1, 1, 5, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0111_semantics :
    ((Generated.hostChunk009[3]).induced.toList, (Generated.hostChunk009[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[3]).mask)) := by
  have hm : (Generated.hostChunk009[3]).mask = 2522 := by decide +kernel
  have hv : ((Generated.hostChunk009[3]).induced.toList, (Generated.hostChunk009[3]).complement.toList) =
      ([0, 1, 3, 1, 0, 1, 1, 5, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0111]

theorem fixed_values_0112 :
    (fixedDensityCounts (maskGraph 7 2523), fixedComplementCounts (maskGraph 7 2523)) =
      ([0, 1, 3, 1, 0, 1, 0, 3, 5, 0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0112_semantics :
    ((Generated.hostChunk009[4]).induced.toList, (Generated.hostChunk009[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[4]).mask)) := by
  have hm : (Generated.hostChunk009[4]).mask = 2523 := by decide +kernel
  have hv : ((Generated.hostChunk009[4]).induced.toList, (Generated.hostChunk009[4]).complement.toList) =
      ([0, 1, 3, 1, 0, 1, 0, 3, 5, 0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0112]

theorem fixed_values_0113 :
    (fixedDensityCounts (maskGraph 7 2526), fixedComplementCounts (maskGraph 7 2526)) =
      ([0, 1, 2, 2, 0, 1, 0, 3, 4, 0, 0, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 2, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0113_semantics :
    ((Generated.hostChunk009[5]).induced.toList, (Generated.hostChunk009[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[5]).mask)) := by
  have hm : (Generated.hostChunk009[5]).mask = 2526 := by decide +kernel
  have hv : ((Generated.hostChunk009[5]).induced.toList, (Generated.hostChunk009[5]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 0, 3, 4, 0, 0, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 2, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0113]

theorem fixed_values_0114 :
    (fixedDensityCounts (maskGraph 7 2527), fixedComplementCounts (maskGraph 7 2527)) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 7, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 2, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0114_semantics :
    ((Generated.hostChunk009[6]).induced.toList, (Generated.hostChunk009[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[6]).mask)) := by
  have hm : (Generated.hostChunk009[6]).mask = 2527 := by decide +kernel
  have hv : ((Generated.hostChunk009[6]).induced.toList, (Generated.hostChunk009[6]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 7, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 2, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0114]

theorem fixed_values_0115 :
    (fixedDensityCounts (maskGraph 7 2544), fixedComplementCounts (maskGraph 7 2544)) =
      ([0, 1, 4, 0, 0, 1, 2, 0, 3, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0115_semantics :
    ((Generated.hostChunk009[7]).induced.toList, (Generated.hostChunk009[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[7]).mask)) := by
  have hm : (Generated.hostChunk009[7]).mask = 2544 := by decide +kernel
  have hv : ((Generated.hostChunk009[7]).induced.toList, (Generated.hostChunk009[7]).complement.toList) =
      ([0, 1, 4, 0, 0, 1, 2, 0, 3, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0115]

theorem fixed_values_0116 :
    (fixedDensityCounts (maskGraph 7 2545), fixedComplementCounts (maskGraph 7 2545)) =
      ([0, 1, 4, 0, 0, 1, 2, 0, 2, 1, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0116_semantics :
    ((Generated.hostChunk009[8]).induced.toList, (Generated.hostChunk009[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[8]).mask)) := by
  have hm : (Generated.hostChunk009[8]).mask = 2545 := by decide +kernel
  have hv : ((Generated.hostChunk009[8]).induced.toList, (Generated.hostChunk009[8]).complement.toList) =
      ([0, 1, 4, 0, 0, 1, 2, 0, 2, 1, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0116]

theorem fixed_values_0117 :
    (fixedDensityCounts (maskGraph 7 2546), fixedComplementCounts (maskGraph 7 2546)) =
      ([0, 1, 3, 1, 0, 1, 0, 2, 2, 4, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0117_semantics :
    ((Generated.hostChunk009[9]).induced.toList, (Generated.hostChunk009[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[9]).mask)) := by
  have hm : (Generated.hostChunk009[9]).mask = 2546 := by decide +kernel
  have hv : ((Generated.hostChunk009[9]).induced.toList, (Generated.hostChunk009[9]).complement.toList) =
      ([0, 1, 3, 1, 0, 1, 0, 2, 2, 4, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0117]

theorem fixed_values_0118 :
    (fixedDensityCounts (maskGraph 7 2547), fixedComplementCounts (maskGraph 7 2547)) =
      ([0, 1, 3, 1, 0, 1, 0, 2, 2, 0, 5, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0118_semantics :
    ((Generated.hostChunk009[10]).induced.toList, (Generated.hostChunk009[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[10]).mask)) := by
  have hm : (Generated.hostChunk009[10]).mask = 2547 := by decide +kernel
  have hv : ((Generated.hostChunk009[10]).induced.toList, (Generated.hostChunk009[10]).complement.toList) =
      ([0, 1, 3, 1, 0, 1, 0, 2, 2, 0, 5, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0118]

theorem fixed_values_0119 :
    (fixedDensityCounts (maskGraph 7 2550), fixedComplementCounts (maskGraph 7 2550)) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 4, 1, 2, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0119_semantics :
    ((Generated.hostChunk009[11]).induced.toList, (Generated.hostChunk009[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk009[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk009[11]).mask)) := by
  have hm : (Generated.hostChunk009[11]).mask = 2550 := by decide +kernel
  have hv : ((Generated.hostChunk009[11]).induced.toList, (Generated.hostChunk009[11]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 4, 1, 2, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0119]

theorem fixed_chunk_009_semantics :
    ∀ h ∈ Generated.hostChunk009.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk009.toList = [Generated.hostChunk009[0], Generated.hostChunk009[1], Generated.hostChunk009[2], Generated.hostChunk009[3], Generated.hostChunk009[4], Generated.hostChunk009[5], Generated.hostChunk009[6], Generated.hostChunk009[7], Generated.hostChunk009[8], Generated.hostChunk009[9], Generated.hostChunk009[10], Generated.hostChunk009[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0108_semantics
  · exact fixed_host_0109_semantics
  · exact fixed_host_0110_semantics
  · exact fixed_host_0111_semantics
  · exact fixed_host_0112_semantics
  · exact fixed_host_0113_semantics
  · exact fixed_host_0114_semantics
  · exact fixed_host_0115_semantics
  · exact fixed_host_0116_semantics
  · exact fixed_host_0117_semantics
  · exact fixed_host_0118_semantics
  · exact fixed_host_0119_semantics

end InducedPentagons.Paper

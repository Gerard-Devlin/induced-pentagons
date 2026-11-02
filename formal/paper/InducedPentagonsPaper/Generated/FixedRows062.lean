import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData062
import InducedPentagonsPaper.Generated.FixedRows054

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0744 :
    (fixedDensityCounts (maskGraph 7 59071), fixedComplementCounts (maskGraph 7 59071)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 0, 1, 6, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0744_semantics :
    ((Generated.hostChunk062[0]).induced.toList, (Generated.hostChunk062[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[0]).mask)) := by
  have hm : (Generated.hostChunk062[0]).mask = 59071 := by decide +kernel
  have hv : ((Generated.hostChunk062[0]).induced.toList, (Generated.hostChunk062[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 0, 1, 6, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0744]

theorem fixed_values_0745 :
    (fixedDensityCounts (maskGraph 7 59126), fixedComplementCounts (maskGraph 7 59126)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 4, 0, 0, 3, 2, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0745_semantics :
    ((Generated.hostChunk062[1]).induced.toList, (Generated.hostChunk062[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[1]).mask)) := by
  have hm : (Generated.hostChunk062[1]).mask = 59126 := by decide +kernel
  have hv : ((Generated.hostChunk062[1]).induced.toList, (Generated.hostChunk062[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 4, 0, 0, 3, 2, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0745]

theorem fixed_values_0746 :
    (fixedDensityCounts (maskGraph 7 59127), fixedComplementCounts (maskGraph 7 59127)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 2, 0, 1, 2, 0, 4, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0746_semantics :
    ((Generated.hostChunk062[2]).induced.toList, (Generated.hostChunk062[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[2]).mask)) := by
  have hm : (Generated.hostChunk062[2]).mask = 59127 := by decide +kernel
  have hv : ((Generated.hostChunk062[2]).induced.toList, (Generated.hostChunk062[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 2, 0, 1, 2, 0, 4, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0746]

theorem fixed_values_0747 :
    (fixedDensityCounts (maskGraph 7 59130), fixedComplementCounts (maskGraph 7 59130)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0, 0, 4, 4, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0747_semantics :
    ((Generated.hostChunk062[3]).induced.toList, (Generated.hostChunk062[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[3]).mask)) := by
  have hm : (Generated.hostChunk062[3]).mask = 59130 := by decide +kernel
  have hv : ((Generated.hostChunk062[3]).induced.toList, (Generated.hostChunk062[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0, 0, 4, 4, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0747]

theorem fixed_values_0748 :
    (fixedDensityCounts (maskGraph 7 59131), fixedComplementCounts (maskGraph 7 59131)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0, 3, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0748_semantics :
    ((Generated.hostChunk062[4]).induced.toList, (Generated.hostChunk062[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[4]).mask)) := by
  have hm : (Generated.hostChunk062[4]).mask = 59131 := by decide +kernel
  have hv : ((Generated.hostChunk062[4]).induced.toList, (Generated.hostChunk062[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0, 3, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0748]

theorem fixed_values_0749 :
    (fixedDensityCounts (maskGraph 7 59132), fixedComplementCounts (maskGraph 7 59132)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 3, 1, 1, 0, 0, 0, 7, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0749_semantics :
    ((Generated.hostChunk062[5]).induced.toList, (Generated.hostChunk062[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[5]).mask)) := by
  have hm : (Generated.hostChunk062[5]).mask = 59132 := by decide +kernel
  have hv : ((Generated.hostChunk062[5]).induced.toList, (Generated.hostChunk062[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 3, 1, 1, 0, 0, 0, 7, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0749]

theorem fixed_values_0750 :
    (fixedDensityCounts (maskGraph 7 59133), fixedComplementCounts (maskGraph 7 59133)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 4, 3, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0750_semantics :
    ((Generated.hostChunk062[6]).induced.toList, (Generated.hostChunk062[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[6]).mask)) := by
  have hm : (Generated.hostChunk062[6]).mask = 59133 := by decide +kernel
  have hv : ((Generated.hostChunk062[6]).induced.toList, (Generated.hostChunk062[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 4, 3, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0750]

theorem fixed_values_0751 :
    (fixedDensityCounts (maskGraph 7 59134), fixedComplementCounts (maskGraph 7 59134)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 3, 1, 0, 0, 0, 2, 2, 0, 2, 0, 3, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0751_semantics :
    ((Generated.hostChunk062[7]).induced.toList, (Generated.hostChunk062[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[7]).mask)) := by
  have hm : (Generated.hostChunk062[7]).mask = 59134 := by decide +kernel
  have hv : ((Generated.hostChunk062[7]).induced.toList, (Generated.hostChunk062[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 3, 1, 0, 0, 0, 2, 2, 0, 2, 0, 3, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0751]

theorem fixed_values_0752 :
    (fixedDensityCounts (maskGraph 7 59135), fixedComplementCounts (maskGraph 7 59135)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 3, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0752_semantics :
    ((Generated.hostChunk062[8]).induced.toList, (Generated.hostChunk062[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[8]).mask)) := by
  have hm : (Generated.hostChunk062[8]).mask = 59135 := by decide +kernel
  have hv : ((Generated.hostChunk062[8]).induced.toList, (Generated.hostChunk062[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 3, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0752]

theorem fixed_values_0753 :
    (fixedDensityCounts (maskGraph 7 59324), fixedComplementCounts (maskGraph 7 59324)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 8, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0753_semantics :
    ((Generated.hostChunk062[9]).induced.toList, (Generated.hostChunk062[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[9]).mask)) := by
  have hm : (Generated.hostChunk062[9]).mask = 59324 := by decide +kernel
  have hv : ((Generated.hostChunk062[9]).induced.toList, (Generated.hostChunk062[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 8, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0753]

theorem fixed_values_0754 :
    (fixedDensityCounts (maskGraph 7 59325), fixedComplementCounts (maskGraph 7 59325)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 4, 0, 0, 2, 1, 0, 4, 4, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0754_semantics :
    ((Generated.hostChunk062[10]).induced.toList, (Generated.hostChunk062[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[10]).mask)) := by
  have hm : (Generated.hostChunk062[10]).mask = 59325 := by decide +kernel
  have hv : ((Generated.hostChunk062[10]).induced.toList, (Generated.hostChunk062[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 4, 0, 0, 2, 1, 0, 4, 4, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0754]

theorem fixed_values_0755 :
    (fixedDensityCounts (maskGraph 7 59326), fixedComplementCounts (maskGraph 7 59326)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2, 1, 0, 2, 0, 4, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0755_semantics :
    ((Generated.hostChunk062[11]).induced.toList, (Generated.hostChunk062[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk062[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk062[11]).mask)) := by
  have hm : (Generated.hostChunk062[11]).mask = 59326 := by decide +kernel
  have hv : ((Generated.hostChunk062[11]).induced.toList, (Generated.hostChunk062[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2, 1, 0, 2, 0, 4, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0755]

theorem fixed_chunk_062_semantics :
    ∀ h ∈ Generated.hostChunk062.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk062.toList = [Generated.hostChunk062[0], Generated.hostChunk062[1], Generated.hostChunk062[2], Generated.hostChunk062[3], Generated.hostChunk062[4], Generated.hostChunk062[5], Generated.hostChunk062[6], Generated.hostChunk062[7], Generated.hostChunk062[8], Generated.hostChunk062[9], Generated.hostChunk062[10], Generated.hostChunk062[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0744_semantics
  · exact fixed_host_0745_semantics
  · exact fixed_host_0746_semantics
  · exact fixed_host_0747_semantics
  · exact fixed_host_0748_semantics
  · exact fixed_host_0749_semantics
  · exact fixed_host_0750_semantics
  · exact fixed_host_0751_semantics
  · exact fixed_host_0752_semantics
  · exact fixed_host_0753_semantics
  · exact fixed_host_0754_semantics
  · exact fixed_host_0755_semantics

end InducedPentagons.Paper

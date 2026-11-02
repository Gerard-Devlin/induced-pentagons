import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData063
import InducedPentagonsPaper.Generated.FixedRows055

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0756 :
    (fixedDensityCounts (maskGraph 7 59327), fixedComplementCounts (maskGraph 7 59327)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 1, 2, 0, 0, 4, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0756_semantics :
    ((Generated.hostChunk063[0]).induced.toList, (Generated.hostChunk063[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[0]).mask)) := by
  have hm : (Generated.hostChunk063[0]).mask = 59327 := by decide +kernel
  have hv : ((Generated.hostChunk063[0]).induced.toList, (Generated.hostChunk063[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 1, 2, 0, 0, 4, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0756]

theorem fixed_values_0757 :
    (fixedDensityCounts (maskGraph 7 59390), fixedComplementCounts (maskGraph 7 59390)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 7, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0757_semantics :
    ((Generated.hostChunk063[1]).induced.toList, (Generated.hostChunk063[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[1]).mask)) := by
  have hm : (Generated.hostChunk063[1]).mask = 59390 := by decide +kernel
  have hv : ((Generated.hostChunk063[1]).induced.toList, (Generated.hostChunk063[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 7, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0757]

theorem fixed_values_0758 :
    (fixedDensityCounts (maskGraph 7 59391), fixedComplementCounts (maskGraph 7 59391)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 7, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0758_semantics :
    ((Generated.hostChunk063[2]).induced.toList, (Generated.hostChunk063[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[2]).mask)) := by
  have hm : (Generated.hostChunk063[2]).mask = 59391 := by decide +kernel
  have hv : ((Generated.hostChunk063[2]).induced.toList, (Generated.hostChunk063[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 7, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0758]

theorem fixed_values_0759 :
    (fixedDensityCounts (maskGraph 7 61111), fixedComplementCounts (maskGraph 7 61111)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 4, 0, 0, 2, 1, 1, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0759_semantics :
    ((Generated.hostChunk063[3]).induced.toList, (Generated.hostChunk063[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[3]).mask)) := by
  have hm : (Generated.hostChunk063[3]).mask = 61111 := by decide +kernel
  have hv : ((Generated.hostChunk063[3]).induced.toList, (Generated.hostChunk063[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 4, 0, 0, 2, 1, 1, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0759]

theorem fixed_values_0760 :
    (fixedDensityCounts (maskGraph 7 61112), fixedComplementCounts (maskGraph 7 61112)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0760_semantics :
    ((Generated.hostChunk063[4]).induced.toList, (Generated.hostChunk063[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[4]).mask)) := by
  have hm : (Generated.hostChunk063[4]).mask = 61112 := by decide +kernel
  have hv : ((Generated.hostChunk063[4]).induced.toList, (Generated.hostChunk063[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0760]

theorem fixed_values_0761 :
    (fixedDensityCounts (maskGraph 7 61113), fixedComplementCounts (maskGraph 7 61113)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 2, 5, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0761_semantics :
    ((Generated.hostChunk063[5]).induced.toList, (Generated.hostChunk063[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[5]).mask)) := by
  have hm : (Generated.hostChunk063[5]).mask = 61113 := by decide +kernel
  have hv : ((Generated.hostChunk063[5]).induced.toList, (Generated.hostChunk063[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 2, 5, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0761]

theorem fixed_values_0762 :
    (fixedDensityCounts (maskGraph 7 61115), fixedComplementCounts (maskGraph 7 61115)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 2, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0762_semantics :
    ((Generated.hostChunk063[6]).induced.toList, (Generated.hostChunk063[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[6]).mask)) := by
  have hm : (Generated.hostChunk063[6]).mask = 61115 := by decide +kernel
  have hv : ((Generated.hostChunk063[6]).induced.toList, (Generated.hostChunk063[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 2, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0762]

theorem fixed_values_0763 :
    (fixedDensityCounts (maskGraph 7 61116), fixedComplementCounts (maskGraph 7 61116)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 1, 0, 0, 0, 4, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0763_semantics :
    ((Generated.hostChunk063[7]).induced.toList, (Generated.hostChunk063[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[7]).mask)) := by
  have hm : (Generated.hostChunk063[7]).mask = 61116 := by decide +kernel
  have hv : ((Generated.hostChunk063[7]).induced.toList, (Generated.hostChunk063[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 1, 0, 0, 0, 4, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0763]

theorem fixed_values_0764 :
    (fixedDensityCounts (maskGraph 7 61117), fixedComplementCounts (maskGraph 7 61117)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 2, 3, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0764_semantics :
    ((Generated.hostChunk063[8]).induced.toList, (Generated.hostChunk063[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[8]).mask)) := by
  have hm : (Generated.hostChunk063[8]).mask = 61117 := by decide +kernel
  have hv : ((Generated.hostChunk063[8]).induced.toList, (Generated.hostChunk063[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 2, 3, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0764]

theorem fixed_values_0765 :
    (fixedDensityCounts (maskGraph 7 61119), fixedComplementCounts (maskGraph 7 61119)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 2, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0765_semantics :
    ((Generated.hostChunk063[9]).induced.toList, (Generated.hostChunk063[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[9]).mask)) := by
  have hm : (Generated.hostChunk063[9]).mask = 61119 := by decide +kernel
  have hv : ((Generated.hostChunk063[9]).induced.toList, (Generated.hostChunk063[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 2, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0765]

theorem fixed_values_0766 :
    (fixedDensityCounts (maskGraph 7 61175), fixedComplementCounts (maskGraph 7 61175)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 2, 0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0766_semantics :
    ((Generated.hostChunk063[10]).induced.toList, (Generated.hostChunk063[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[10]).mask)) := by
  have hm : (Generated.hostChunk063[10]).mask = 61175 := by decide +kernel
  have hv : ((Generated.hostChunk063[10]).induced.toList, (Generated.hostChunk063[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 2, 0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0766]

theorem fixed_values_0767 :
    (fixedDensityCounts (maskGraph 7 61176), fixedComplementCounts (maskGraph 7 61176)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 3, 4, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0767_semantics :
    ((Generated.hostChunk063[11]).induced.toList, (Generated.hostChunk063[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk063[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk063[11]).mask)) := by
  have hm : (Generated.hostChunk063[11]).mask = 61176 := by decide +kernel
  have hv : ((Generated.hostChunk063[11]).induced.toList, (Generated.hostChunk063[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 3, 4, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0767]

theorem fixed_chunk_063_semantics :
    ∀ h ∈ Generated.hostChunk063.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk063.toList = [Generated.hostChunk063[0], Generated.hostChunk063[1], Generated.hostChunk063[2], Generated.hostChunk063[3], Generated.hostChunk063[4], Generated.hostChunk063[5], Generated.hostChunk063[6], Generated.hostChunk063[7], Generated.hostChunk063[8], Generated.hostChunk063[9], Generated.hostChunk063[10], Generated.hostChunk063[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0756_semantics
  · exact fixed_host_0757_semantics
  · exact fixed_host_0758_semantics
  · exact fixed_host_0759_semantics
  · exact fixed_host_0760_semantics
  · exact fixed_host_0761_semantics
  · exact fixed_host_0762_semantics
  · exact fixed_host_0763_semantics
  · exact fixed_host_0764_semantics
  · exact fixed_host_0765_semantics
  · exact fixed_host_0766_semantics
  · exact fixed_host_0767_semantics

end InducedPentagons.Paper

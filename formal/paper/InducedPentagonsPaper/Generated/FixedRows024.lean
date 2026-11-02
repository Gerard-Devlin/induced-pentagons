import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData024
import InducedPentagonsPaper.Generated.FixedRows016

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0288 :
    (fixedDensityCounts (maskGraph 7 7165), fixedComplementCounts (maskGraph 7 7165)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 2, 4, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0288_semantics :
    ((Generated.hostChunk024[0]).induced.toList, (Generated.hostChunk024[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[0]).mask)) := by
  have hm : (Generated.hostChunk024[0]).mask = 7165 := by decide +kernel
  have hv : ((Generated.hostChunk024[0]).induced.toList, (Generated.hostChunk024[0]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 2, 4, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0288]

theorem fixed_values_0289 :
    (fixedDensityCounts (maskGraph 7 7166), fixedComplementCounts (maskGraph 7 7166)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 4, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0289_semantics :
    ((Generated.hostChunk024[1]).induced.toList, (Generated.hostChunk024[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[1]).mask)) := by
  have hm : (Generated.hostChunk024[1]).mask = 7166 := by decide +kernel
  have hv : ((Generated.hostChunk024[1]).induced.toList, (Generated.hostChunk024[1]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 4, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0289]

theorem fixed_values_0290 :
    (fixedDensityCounts (maskGraph 7 7167), fixedComplementCounts (maskGraph 7 7167)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 7, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0290_semantics :
    ((Generated.hostChunk024[2]).induced.toList, (Generated.hostChunk024[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[2]).mask)) := by
  have hm : (Generated.hostChunk024[2]).mask = 7167 := by decide +kernel
  have hv : ((Generated.hostChunk024[2]).induced.toList, (Generated.hostChunk024[2]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 7, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0290]

theorem fixed_values_0291 :
    (fixedDensityCounts (maskGraph 7 7740), fixedComplementCounts (maskGraph 7 7740)) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 4, 0, 2, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0291_semantics :
    ((Generated.hostChunk024[3]).induced.toList, (Generated.hostChunk024[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[3]).mask)) := by
  have hm : (Generated.hostChunk024[3]).mask = 7740 := by decide +kernel
  have hv : ((Generated.hostChunk024[3]).induced.toList, (Generated.hostChunk024[3]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 4, 0, 2, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0291]

theorem fixed_values_0292 :
    (fixedDensityCounts (maskGraph 7 7741), fixedComplementCounts (maskGraph 7 7741)) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 2, 2, 0, 1, 0, 0, 3, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0292_semantics :
    ((Generated.hostChunk024[4]).induced.toList, (Generated.hostChunk024[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[4]).mask)) := by
  have hm : (Generated.hostChunk024[4]).mask = 7741 := by decide +kernel
  have hv : ((Generated.hostChunk024[4]).induced.toList, (Generated.hostChunk024[4]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 2, 2, 0, 1, 0, 0, 3, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0292]

theorem fixed_values_0293 :
    (fixedDensityCounts (maskGraph 7 7743), fixedComplementCounts (maskGraph 7 7743)) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0293_semantics :
    ((Generated.hostChunk024[5]).induced.toList, (Generated.hostChunk024[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[5]).mask)) := by
  have hm : (Generated.hostChunk024[5]).mask = 7743 := by decide +kernel
  have hv : ((Generated.hostChunk024[5]).induced.toList, (Generated.hostChunk024[5]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0293]

theorem fixed_values_0294 :
    (fixedDensityCounts (maskGraph 7 7804), fixedComplementCounts (maskGraph 7 7804)) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0294_semantics :
    ((Generated.hostChunk024[6]).induced.toList, (Generated.hostChunk024[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[6]).mask)) := by
  have hm : (Generated.hostChunk024[6]).mask = 7804 := by decide +kernel
  have hv : ((Generated.hostChunk024[6]).induced.toList, (Generated.hostChunk024[6]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0294]

theorem fixed_values_0295 :
    (fixedDensityCounts (maskGraph 7 7805), fixedComplementCounts (maskGraph 7 7805)) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0295_semantics :
    ((Generated.hostChunk024[7]).induced.toList, (Generated.hostChunk024[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[7]).mask)) := by
  have hm : (Generated.hostChunk024[7]).mask = 7805 := by decide +kernel
  have hv : ((Generated.hostChunk024[7]).induced.toList, (Generated.hostChunk024[7]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0295]

theorem fixed_values_0296 :
    (fixedDensityCounts (maskGraph 7 7807), fixedComplementCounts (maskGraph 7 7807)) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0296_semantics :
    ((Generated.hostChunk024[8]).induced.toList, (Generated.hostChunk024[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[8]).mask)) := by
  have hm : (Generated.hostChunk024[8]).mask = 7807 := by decide +kernel
  have hv : ((Generated.hostChunk024[8]).induced.toList, (Generated.hostChunk024[8]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0296]

theorem fixed_values_0297 :
    (fixedDensityCounts (maskGraph 7 7860), fixedComplementCounts (maskGraph 7 7860)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 4, 3, 0, 4, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0297_semantics :
    ((Generated.hostChunk024[9]).induced.toList, (Generated.hostChunk024[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[9]).mask)) := by
  have hm : (Generated.hostChunk024[9]).mask = 7860 := by decide +kernel
  have hv : ((Generated.hostChunk024[9]).induced.toList, (Generated.hostChunk024[9]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 4, 3, 0, 4, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0297]

theorem fixed_values_0298 :
    (fixedDensityCounts (maskGraph 7 7861), fixedComplementCounts (maskGraph 7 7861)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 4, 4, 0, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0298_semantics :
    ((Generated.hostChunk024[10]).induced.toList, (Generated.hostChunk024[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[10]).mask)) := by
  have hm : (Generated.hostChunk024[10]).mask = 7861 := by decide +kernel
  have hv : ((Generated.hostChunk024[10]).induced.toList, (Generated.hostChunk024[10]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 4, 4, 0, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0298]

theorem fixed_values_0299 :
    (fixedDensityCounts (maskGraph 7 7862), fixedComplementCounts (maskGraph 7 7862)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 3, 0, 4, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0299_semantics :
    ((Generated.hostChunk024[11]).induced.toList, (Generated.hostChunk024[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk024[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk024[11]).mask)) := by
  have hm : (Generated.hostChunk024[11]).mask = 7862 := by decide +kernel
  have hv : ((Generated.hostChunk024[11]).induced.toList, (Generated.hostChunk024[11]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 3, 0, 4, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0299]

theorem fixed_chunk_024_semantics :
    ∀ h ∈ Generated.hostChunk024.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk024.toList = [Generated.hostChunk024[0], Generated.hostChunk024[1], Generated.hostChunk024[2], Generated.hostChunk024[3], Generated.hostChunk024[4], Generated.hostChunk024[5], Generated.hostChunk024[6], Generated.hostChunk024[7], Generated.hostChunk024[8], Generated.hostChunk024[9], Generated.hostChunk024[10], Generated.hostChunk024[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0288_semantics
  · exact fixed_host_0289_semantics
  · exact fixed_host_0290_semantics
  · exact fixed_host_0291_semantics
  · exact fixed_host_0292_semantics
  · exact fixed_host_0293_semantics
  · exact fixed_host_0294_semantics
  · exact fixed_host_0295_semantics
  · exact fixed_host_0296_semantics
  · exact fixed_host_0297_semantics
  · exact fixed_host_0298_semantics
  · exact fixed_host_0299_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData002

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0024 :
    (fixedDensityCounts (maskGraph 7 206), fixedComplementCounts (maskGraph 7 206)) =
      ([1, 3, 8, 2, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0024_semantics :
    ((Generated.hostChunk002[0]).induced.toList, (Generated.hostChunk002[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[0]).mask)) := by
  have hm : (Generated.hostChunk002[0]).mask = 206 := by decide +kernel
  have hv : ((Generated.hostChunk002[0]).induced.toList, (Generated.hostChunk002[0]).complement.toList) =
      ([1, 3, 8, 2, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0024]

theorem fixed_values_0025 :
    (fixedDensityCounts (maskGraph 7 207), fixedComplementCounts (maskGraph 7 207)) =
      ([1, 2, 7, 2, 0, 2, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0025_semantics :
    ((Generated.hostChunk002[1]).induced.toList, (Generated.hostChunk002[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[1]).mask)) := by
  have hm : (Generated.hostChunk002[1]).mask = 207 := by decide +kernel
  have hv : ((Generated.hostChunk002[1]).induced.toList, (Generated.hostChunk002[1]).complement.toList) =
      ([1, 2, 7, 2, 0, 2, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0025]

theorem fixed_values_0026 :
    (fixedDensityCounts (maskGraph 7 216), fixedComplementCounts (maskGraph 7 216)) =
      ([1, 4, 8, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0026_semantics :
    ((Generated.hostChunk002[2]).induced.toList, (Generated.hostChunk002[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[2]).mask)) := by
  have hm : (Generated.hostChunk002[2]).mask = 216 := by decide +kernel
  have hv : ((Generated.hostChunk002[2]).induced.toList, (Generated.hostChunk002[2]).complement.toList) =
      ([1, 4, 8, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0026]

theorem fixed_values_0027 :
    (fixedDensityCounts (maskGraph 7 217), fixedComplementCounts (maskGraph 7 217)) =
      ([1, 4, 6, 2, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0027_semantics :
    ((Generated.hostChunk002[3]).induced.toList, (Generated.hostChunk002[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[3]).mask)) := by
  have hm : (Generated.hostChunk002[3]).mask = 217 := by decide +kernel
  have hv : ((Generated.hostChunk002[3]).induced.toList, (Generated.hostChunk002[3]).complement.toList) =
      ([1, 4, 6, 2, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0027]

theorem fixed_values_0028 :
    (fixedDensityCounts (maskGraph 7 218), fixedComplementCounts (maskGraph 7 218)) =
      ([1, 2, 7, 2, 0, 0, 2, 3, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0028_semantics :
    ((Generated.hostChunk002[4]).induced.toList, (Generated.hostChunk002[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[4]).mask)) := by
  have hm : (Generated.hostChunk002[4]).mask = 218 := by decide +kernel
  have hv : ((Generated.hostChunk002[4]).induced.toList, (Generated.hostChunk002[4]).complement.toList) =
      ([1, 2, 7, 2, 0, 0, 2, 3, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0028]

theorem fixed_values_0029 :
    (fixedDensityCounts (maskGraph 7 219), fixedComplementCounts (maskGraph 7 219)) =
      ([1, 2, 6, 3, 0, 0, 0, 2, 3, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0029_semantics :
    ((Generated.hostChunk002[5]).induced.toList, (Generated.hostChunk002[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[5]).mask)) := by
  have hm : (Generated.hostChunk002[5]).mask = 219 := by decide +kernel
  have hv : ((Generated.hostChunk002[5]).induced.toList, (Generated.hostChunk002[5]).complement.toList) =
      ([1, 2, 6, 3, 0, 0, 0, 2, 3, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0029]

theorem fixed_values_0030 :
    (fixedDensityCounts (maskGraph 7 222), fixedComplementCounts (maskGraph 7 222)) =
      ([1, 2, 4, 4, 1, 0, 0, 4, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0030_semantics :
    ((Generated.hostChunk002[6]).induced.toList, (Generated.hostChunk002[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[6]).mask)) := by
  have hm : (Generated.hostChunk002[6]).mask = 222 := by decide +kernel
  have hv : ((Generated.hostChunk002[6]).induced.toList, (Generated.hostChunk002[6]).complement.toList) =
      ([1, 2, 4, 4, 1, 0, 0, 4, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0030]

theorem fixed_values_0031 :
    (fixedDensityCounts (maskGraph 7 223), fixedComplementCounts (maskGraph 7 223)) =
      ([1, 2, 3, 5, 1, 0, 0, 0, 4, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0031_semantics :
    ((Generated.hostChunk002[7]).induced.toList, (Generated.hostChunk002[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[7]).mask)) := by
  have hm : (Generated.hostChunk002[7]).mask = 223 := by decide +kernel
  have hv : ((Generated.hostChunk002[7]).induced.toList, (Generated.hostChunk002[7]).complement.toList) =
      ([1, 2, 3, 5, 1, 0, 0, 0, 4, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0031]

theorem fixed_values_0032 :
    (fixedDensityCounts (maskGraph 7 248), fixedComplementCounts (maskGraph 7 248)) =
      ([1, 2, 6, 3, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0032_semantics :
    ((Generated.hostChunk002[8]).induced.toList, (Generated.hostChunk002[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[8]).mask)) := by
  have hm : (Generated.hostChunk002[8]).mask = 248 := by decide +kernel
  have hv : ((Generated.hostChunk002[8]).induced.toList, (Generated.hostChunk002[8]).complement.toList) =
      ([1, 2, 6, 3, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0032]

theorem fixed_values_0033 :
    (fixedDensityCounts (maskGraph 7 249), fixedComplementCounts (maskGraph 7 249)) =
      ([1, 2, 6, 2, 1, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0033_semantics :
    ((Generated.hostChunk002[9]).induced.toList, (Generated.hostChunk002[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[9]).mask)) := by
  have hm : (Generated.hostChunk002[9]).mask = 249 := by decide +kernel
  have hv : ((Generated.hostChunk002[9]).induced.toList, (Generated.hostChunk002[9]).complement.toList) =
      ([1, 2, 6, 2, 1, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0033]

theorem fixed_values_0034 :
    (fixedDensityCounts (maskGraph 7 250), fixedComplementCounts (maskGraph 7 250)) =
      ([1, 2, 3, 5, 1, 0, 0, 0, 0, 3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0034_semantics :
    ((Generated.hostChunk002[10]).induced.toList, (Generated.hostChunk002[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[10]).mask)) := by
  have hm : (Generated.hostChunk002[10]).mask = 250 := by decide +kernel
  have hv : ((Generated.hostChunk002[10]).induced.toList, (Generated.hostChunk002[10]).complement.toList) =
      ([1, 2, 3, 5, 1, 0, 0, 0, 0, 3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0034]

theorem fixed_values_0035 :
    (fixedDensityCounts (maskGraph 7 251), fixedComplementCounts (maskGraph 7 251)) =
      ([1, 2, 3, 4, 2, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0035_semantics :
    ((Generated.hostChunk002[11]).induced.toList, (Generated.hostChunk002[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk002[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk002[11]).mask)) := by
  have hm : (Generated.hostChunk002[11]).mask = 251 := by decide +kernel
  have hv : ((Generated.hostChunk002[11]).induced.toList, (Generated.hostChunk002[11]).complement.toList) =
      ([1, 2, 3, 4, 2, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0035]

theorem fixed_chunk_002_semantics :
    ∀ h ∈ Generated.hostChunk002.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk002.toList = [Generated.hostChunk002[0], Generated.hostChunk002[1], Generated.hostChunk002[2], Generated.hostChunk002[3], Generated.hostChunk002[4], Generated.hostChunk002[5], Generated.hostChunk002[6], Generated.hostChunk002[7], Generated.hostChunk002[8], Generated.hostChunk002[9], Generated.hostChunk002[10], Generated.hostChunk002[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0024_semantics
  · exact fixed_host_0025_semantics
  · exact fixed_host_0026_semantics
  · exact fixed_host_0027_semantics
  · exact fixed_host_0028_semantics
  · exact fixed_host_0029_semantics
  · exact fixed_host_0030_semantics
  · exact fixed_host_0031_semantics
  · exact fixed_host_0032_semantics
  · exact fixed_host_0033_semantics
  · exact fixed_host_0034_semantics
  · exact fixed_host_0035_semantics

end InducedPentagons.Paper

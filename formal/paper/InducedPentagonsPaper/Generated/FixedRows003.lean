import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData003

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0036 :
    (fixedDensityCounts (maskGraph 7 254), fixedComplementCounts (maskGraph 7 254)) =
      ([1, 2, 3, 1, 5, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0036_semantics :
    ((Generated.hostChunk003[0]).induced.toList, (Generated.hostChunk003[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[0]).mask)) := by
  have hm : (Generated.hostChunk003[0]).mask = 254 := by decide +kernel
  have hv : ((Generated.hostChunk003[0]).induced.toList, (Generated.hostChunk003[0]).complement.toList) =
      ([1, 2, 3, 1, 5, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0036]

theorem fixed_values_0037 :
    (fixedDensityCounts (maskGraph 7 255), fixedComplementCounts (maskGraph 7 255)) =
      ([1, 2, 3, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0037_semantics :
    ((Generated.hostChunk003[1]).induced.toList, (Generated.hostChunk003[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[1]).mask)) := by
  have hm : (Generated.hostChunk003[1]).mask = 255 := by decide +kernel
  have hv : ((Generated.hostChunk003[1]).induced.toList, (Generated.hostChunk003[1]).complement.toList) =
      ([1, 2, 3, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0037]

theorem fixed_values_0038 :
    (fixedDensityCounts (maskGraph 7 462), fixedComplementCounts (maskGraph 7 462)) =
      ([1, 0, 9, 4, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0038_semantics :
    ((Generated.hostChunk003[2]).induced.toList, (Generated.hostChunk003[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[2]).mask)) := by
  have hm : (Generated.hostChunk003[2]).mask = 462 := by decide +kernel
  have hv : ((Generated.hostChunk003[2]).induced.toList, (Generated.hostChunk003[2]).complement.toList) =
      ([1, 0, 9, 4, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0038]

theorem fixed_values_0039 :
    (fixedDensityCounts (maskGraph 7 463), fixedComplementCounts (maskGraph 7 463)) =
      ([1, 0, 6, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0039_semantics :
    ((Generated.hostChunk003[3]).induced.toList, (Generated.hostChunk003[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[3]).mask)) := by
  have hm : (Generated.hostChunk003[3]).mask = 463 := by decide +kernel
  have hv : ((Generated.hostChunk003[3]).induced.toList, (Generated.hostChunk003[3]).complement.toList) =
      ([1, 0, 6, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0039]

theorem fixed_values_0040 :
    (fixedDensityCounts (maskGraph 7 470), fixedComplementCounts (maskGraph 7 470)) =
      ([1, 0, 6, 4, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0040_semantics :
    ((Generated.hostChunk003[4]).induced.toList, (Generated.hostChunk003[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[4]).mask)) := by
  have hm : (Generated.hostChunk003[4]).mask = 470 := by decide +kernel
  have hv : ((Generated.hostChunk003[4]).induced.toList, (Generated.hostChunk003[4]).complement.toList) =
      ([1, 0, 6, 4, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0040]

theorem fixed_values_0041 :
    (fixedDensityCounts (maskGraph 7 471), fixedComplementCounts (maskGraph 7 471)) =
      ([1, 0, 6, 4, 0, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0041_semantics :
    ((Generated.hostChunk003[5]).induced.toList, (Generated.hostChunk003[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[5]).mask)) := by
  have hm : (Generated.hostChunk003[5]).mask = 471 := by decide +kernel
  have hv : ((Generated.hostChunk003[5]).induced.toList, (Generated.hostChunk003[5]).complement.toList) =
      ([1, 0, 6, 4, 0, 0, 0, 1, 4, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0041]

theorem fixed_values_0042 :
    (fixedDensityCounts (maskGraph 7 478), fixedComplementCounts (maskGraph 7 478)) =
      ([1, 0, 3, 6, 1, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0042_semantics :
    ((Generated.hostChunk003[6]).induced.toList, (Generated.hostChunk003[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[6]).mask)) := by
  have hm : (Generated.hostChunk003[6]).mask = 478 := by decide +kernel
  have hv : ((Generated.hostChunk003[6]).induced.toList, (Generated.hostChunk003[6]).complement.toList) =
      ([1, 0, 3, 6, 1, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0042]

theorem fixed_values_0043 :
    (fixedDensityCounts (maskGraph 7 479), fixedComplementCounts (maskGraph 7 479)) =
      ([1, 0, 3, 6, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0043_semantics :
    ((Generated.hostChunk003[7]).induced.toList, (Generated.hostChunk003[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[7]).mask)) := by
  have hm : (Generated.hostChunk003[7]).mask = 479 := by decide +kernel
  have hv : ((Generated.hostChunk003[7]).induced.toList, (Generated.hostChunk003[7]).complement.toList) =
      ([1, 0, 3, 6, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0043]

theorem fixed_values_0044 :
    (fixedDensityCounts (maskGraph 7 498), fixedComplementCounts (maskGraph 7 498)) =
      ([1, 0, 6, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0044_semantics :
    ((Generated.hostChunk003[8]).induced.toList, (Generated.hostChunk003[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[8]).mask)) := by
  have hm : (Generated.hostChunk003[8]).mask = 498 := by decide +kernel
  have hv : ((Generated.hostChunk003[8]).induced.toList, (Generated.hostChunk003[8]).complement.toList) =
      ([1, 0, 6, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0044]

theorem fixed_values_0045 :
    (fixedDensityCounts (maskGraph 7 499), fixedComplementCounts (maskGraph 7 499)) =
      ([1, 0, 6, 4, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0045_semantics :
    ((Generated.hostChunk003[9]).induced.toList, (Generated.hostChunk003[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[9]).mask)) := by
  have hm : (Generated.hostChunk003[9]).mask = 499 := by decide +kernel
  have hv : ((Generated.hostChunk003[9]).induced.toList, (Generated.hostChunk003[9]).complement.toList) =
      ([1, 0, 6, 4, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0045]

theorem fixed_values_0046 :
    (fixedDensityCounts (maskGraph 7 502), fixedComplementCounts (maskGraph 7 502)) =
      ([1, 0, 3, 6, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0046_semantics :
    ((Generated.hostChunk003[10]).induced.toList, (Generated.hostChunk003[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[10]).mask)) := by
  have hm : (Generated.hostChunk003[10]).mask = 502 := by decide +kernel
  have hv : ((Generated.hostChunk003[10]).induced.toList, (Generated.hostChunk003[10]).complement.toList) =
      ([1, 0, 3, 6, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0046]

theorem fixed_values_0047 :
    (fixedDensityCounts (maskGraph 7 503), fixedComplementCounts (maskGraph 7 503)) =
      ([1, 0, 3, 6, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0047_semantics :
    ((Generated.hostChunk003[11]).induced.toList, (Generated.hostChunk003[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk003[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk003[11]).mask)) := by
  have hm : (Generated.hostChunk003[11]).mask = 503 := by decide +kernel
  have hv : ((Generated.hostChunk003[11]).induced.toList, (Generated.hostChunk003[11]).complement.toList) =
      ([1, 0, 3, 6, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0047]

theorem fixed_chunk_003_semantics :
    ∀ h ∈ Generated.hostChunk003.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk003.toList = [Generated.hostChunk003[0], Generated.hostChunk003[1], Generated.hostChunk003[2], Generated.hostChunk003[3], Generated.hostChunk003[4], Generated.hostChunk003[5], Generated.hostChunk003[6], Generated.hostChunk003[7], Generated.hostChunk003[8], Generated.hostChunk003[9], Generated.hostChunk003[10], Generated.hostChunk003[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0036_semantics
  · exact fixed_host_0037_semantics
  · exact fixed_host_0038_semantics
  · exact fixed_host_0039_semantics
  · exact fixed_host_0040_semantics
  · exact fixed_host_0041_semantics
  · exact fixed_host_0042_semantics
  · exact fixed_host_0043_semantics
  · exact fixed_host_0044_semantics
  · exact fixed_host_0045_semantics
  · exact fixed_host_0046_semantics
  · exact fixed_host_0047_semantics

end InducedPentagons.Paper

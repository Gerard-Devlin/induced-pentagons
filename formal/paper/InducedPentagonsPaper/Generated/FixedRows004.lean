import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData004

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0048 :
    (fixedDensityCounts (maskGraph 7 510), fixedComplementCounts (maskGraph 7 510)) =
      ([1, 0, 3, 2, 5, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0048_semantics :
    ((Generated.hostChunk004[0]).induced.toList, (Generated.hostChunk004[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[0]).mask)) := by
  have hm : (Generated.hostChunk004[0]).mask = 510 := by decide +kernel
  have hv : ((Generated.hostChunk004[0]).induced.toList, (Generated.hostChunk004[0]).complement.toList) =
      ([1, 0, 3, 2, 5, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0048]

theorem fixed_values_0049 :
    (fixedDensityCounts (maskGraph 7 511), fixedComplementCounts (maskGraph 7 511)) =
      ([1, 0, 3, 2, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0049_semantics :
    ((Generated.hostChunk004[1]).induced.toList, (Generated.hostChunk004[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[1]).mask)) := by
  have hm : (Generated.hostChunk004[1]).mask = 511 := by decide +kernel
  have hv : ((Generated.hostChunk004[1]).induced.toList, (Generated.hostChunk004[1]).complement.toList) =
      ([1, 0, 3, 2, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0049]

theorem fixed_values_0050 :
    (fixedDensityCounts (maskGraph 7 990), fixedComplementCounts (maskGraph 7 990)) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0050_semantics :
    ((Generated.hostChunk004[2]).induced.toList, (Generated.hostChunk004[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[2]).mask)) := by
  have hm : (Generated.hostChunk004[2]).mask = 990 := by decide +kernel
  have hv : ((Generated.hostChunk004[2]).induced.toList, (Generated.hostChunk004[2]).complement.toList) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0050]

theorem fixed_values_0051 :
    (fixedDensityCounts (maskGraph 7 991), fixedComplementCounts (maskGraph 7 991)) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0051_semantics :
    ((Generated.hostChunk004[3]).induced.toList, (Generated.hostChunk004[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[3]).mask)) := by
  have hm : (Generated.hostChunk004[3]).mask = 991 := by decide +kernel
  have hv : ((Generated.hostChunk004[3]).induced.toList, (Generated.hostChunk004[3]).complement.toList) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0051]

theorem fixed_values_0052 :
    (fixedDensityCounts (maskGraph 7 1006), fixedComplementCounts (maskGraph 7 1006)) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0052_semantics :
    ((Generated.hostChunk004[4]).induced.toList, (Generated.hostChunk004[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[4]).mask)) := by
  have hm : (Generated.hostChunk004[4]).mask = 1006 := by decide +kernel
  have hv : ((Generated.hostChunk004[4]).induced.toList, (Generated.hostChunk004[4]).complement.toList) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0052]

theorem fixed_values_0053 :
    (fixedDensityCounts (maskGraph 7 1007), fixedComplementCounts (maskGraph 7 1007)) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0053_semantics :
    ((Generated.hostChunk004[5]).induced.toList, (Generated.hostChunk004[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[5]).mask)) := by
  have hm : (Generated.hostChunk004[5]).mask = 1007 := by decide +kernel
  have hv : ((Generated.hostChunk004[5]).induced.toList, (Generated.hostChunk004[5]).complement.toList) =
      ([1, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0053]

theorem fixed_values_0054 :
    (fixedDensityCounts (maskGraph 7 1022), fixedComplementCounts (maskGraph 7 1022)) =
      ([1, 0, 0, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0054_semantics :
    ((Generated.hostChunk004[6]).induced.toList, (Generated.hostChunk004[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[6]).mask)) := by
  have hm : (Generated.hostChunk004[6]).mask = 1022 := by decide +kernel
  have hv : ((Generated.hostChunk004[6]).induced.toList, (Generated.hostChunk004[6]).complement.toList) =
      ([1, 0, 0, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0054]

theorem fixed_values_0055 :
    (fixedDensityCounts (maskGraph 7 1023), fixedComplementCounts (maskGraph 7 1023)) =
      ([1, 0, 0, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0055_semantics :
    ((Generated.hostChunk004[7]).induced.toList, (Generated.hostChunk004[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[7]).mask)) := by
  have hm : (Generated.hostChunk004[7]).mask = 1023 := by decide +kernel
  have hv : ((Generated.hostChunk004[7]).induced.toList, (Generated.hostChunk004[7]).complement.toList) =
      ([1, 0, 0, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0055]

theorem fixed_values_0056 :
    (fixedDensityCounts (maskGraph 7 2046), fixedComplementCounts (maskGraph 7 2046)) =
      ([1, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0056_semantics :
    ((Generated.hostChunk004[8]).induced.toList, (Generated.hostChunk004[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[8]).mask)) := by
  have hm : (Generated.hostChunk004[8]).mask = 2046 := by decide +kernel
  have hv : ((Generated.hostChunk004[8]).induced.toList, (Generated.hostChunk004[8]).complement.toList) =
      ([1, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0056]

theorem fixed_values_0057 :
    (fixedDensityCounts (maskGraph 7 2047), fixedComplementCounts (maskGraph 7 2047)) =
      ([1, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0057_semantics :
    ((Generated.hostChunk004[9]).induced.toList, (Generated.hostChunk004[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[9]).mask)) := by
  have hm : (Generated.hostChunk004[9]).mask = 2047 := by decide +kernel
  have hv : ((Generated.hostChunk004[9]).induced.toList, (Generated.hostChunk004[9]).complement.toList) =
      ([1, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0057]

theorem fixed_values_0058 :
    (fixedDensityCounts (maskGraph 7 2247), fixedComplementCounts (maskGraph 7 2247)) =
      ([0, 6, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0058_semantics :
    ((Generated.hostChunk004[10]).induced.toList, (Generated.hostChunk004[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[10]).mask)) := by
  have hm : (Generated.hostChunk004[10]).mask = 2247 := by decide +kernel
  have hv : ((Generated.hostChunk004[10]).induced.toList, (Generated.hostChunk004[10]).complement.toList) =
      ([0, 6, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0058]

theorem fixed_values_0059 :
    (fixedDensityCounts (maskGraph 7 2248), fixedComplementCounts (maskGraph 7 2248)) =
      ([0, 9, 0, 0, 0, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0059_semantics :
    ((Generated.hostChunk004[11]).induced.toList, (Generated.hostChunk004[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk004[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk004[11]).mask)) := by
  have hm : (Generated.hostChunk004[11]).mask = 2248 := by decide +kernel
  have hv : ((Generated.hostChunk004[11]).induced.toList, (Generated.hostChunk004[11]).complement.toList) =
      ([0, 9, 0, 0, 0, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0059]

theorem fixed_chunk_004_semantics :
    ∀ h ∈ Generated.hostChunk004.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk004.toList = [Generated.hostChunk004[0], Generated.hostChunk004[1], Generated.hostChunk004[2], Generated.hostChunk004[3], Generated.hostChunk004[4], Generated.hostChunk004[5], Generated.hostChunk004[6], Generated.hostChunk004[7], Generated.hostChunk004[8], Generated.hostChunk004[9], Generated.hostChunk004[10], Generated.hostChunk004[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0048_semantics
  · exact fixed_host_0049_semantics
  · exact fixed_host_0050_semantics
  · exact fixed_host_0051_semantics
  · exact fixed_host_0052_semantics
  · exact fixed_host_0053_semantics
  · exact fixed_host_0054_semantics
  · exact fixed_host_0055_semantics
  · exact fixed_host_0056_semantics
  · exact fixed_host_0057_semantics
  · exact fixed_host_0058_semantics
  · exact fixed_host_0059_semantics

end InducedPentagons.Paper

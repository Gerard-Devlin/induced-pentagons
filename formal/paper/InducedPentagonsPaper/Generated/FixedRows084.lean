import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData084
import InducedPentagonsPaper.Generated.FixedRows076

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_1008 :
    (fixedDensityCounts (maskGraph 7 384701), fixedComplementCounts (maskGraph 7 384701)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 5, 4, 2, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 4, 2, 2, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_1008_semantics :
    ((Generated.hostChunk084[0]).induced.toList, (Generated.hostChunk084[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[0]).mask)) := by
  have hm : (Generated.hostChunk084[0]).mask = 384701 := by decide +kernel
  have hv : ((Generated.hostChunk084[0]).induced.toList, (Generated.hostChunk084[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 5, 4, 2, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 4, 2, 2, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1008]

theorem fixed_values_1009 :
    (fixedDensityCounts (maskGraph 7 384703), fixedComplementCounts (maskGraph 7 384703)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 2, 8, 0, 4, 1, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 5, 0, 2, 1, 2, 0]) := by
  decide +kernel

theorem fixed_host_1009_semantics :
    ((Generated.hostChunk084[1]).induced.toList, (Generated.hostChunk084[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[1]).mask)) := by
  have hm : (Generated.hostChunk084[1]).mask = 384703 := by decide +kernel
  have hv : ((Generated.hostChunk084[1]).induced.toList, (Generated.hostChunk084[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 2, 8, 0, 4, 1, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 5, 0, 2, 1, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1009]

theorem fixed_values_1010 :
    (fixedDensityCounts (maskGraph 7 384763), fixedComplementCounts (maskGraph 7 384763)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 6, 0, 3, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 3, 3, 0, 0]) := by
  decide +kernel

theorem fixed_host_1010_semantics :
    ((Generated.hostChunk084[2]).induced.toList, (Generated.hostChunk084[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[2]).mask)) := by
  have hm : (Generated.hostChunk084[2]).mask = 384763 := by decide +kernel
  have hv : ((Generated.hostChunk084[2]).induced.toList, (Generated.hostChunk084[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 6, 0, 3, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 3, 3, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1010]

theorem fixed_values_1011 :
    (fixedDensityCounts (maskGraph 7 384764), fixedComplementCounts (maskGraph 7 384764)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 8, 4, 3, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 2, 3, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_1011_semantics :
    ((Generated.hostChunk084[3]).induced.toList, (Generated.hostChunk084[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[3]).mask)) := by
  have hm : (Generated.hostChunk084[3]).mask = 384764 := by decide +kernel
  have hv : ((Generated.hostChunk084[3]).induced.toList, (Generated.hostChunk084[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 8, 4, 3, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 2, 3, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1011]

theorem fixed_values_1012 :
    (fixedDensityCounts (maskGraph 7 384765), fixedComplementCounts (maskGraph 7 384765)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 3, 5, 3, 3, 3, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 4, 2, 2, 2, 1, 0]) := by
  decide +kernel

theorem fixed_host_1012_semantics :
    ((Generated.hostChunk084[4]).induced.toList, (Generated.hostChunk084[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[4]).mask)) := by
  have hm : (Generated.hostChunk084[4]).mask = 384765 := by decide +kernel
  have hv : ((Generated.hostChunk084[4]).induced.toList, (Generated.hostChunk084[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 3, 5, 3, 3, 3, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 4, 2, 2, 2, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1012]

theorem fixed_values_1013 :
    (fixedDensityCounts (maskGraph 7 384767), fixedComplementCounts (maskGraph 7 384767)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 6, 0, 4, 2, 5, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 4, 0, 4, 1, 3, 0]) := by
  decide +kernel

theorem fixed_host_1013_semantics :
    ((Generated.hostChunk084[5]).induced.toList, (Generated.hostChunk084[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[5]).mask)) := by
  have hm : (Generated.hostChunk084[5]).mask = 384767 := by decide +kernel
  have hv : ((Generated.hostChunk084[5]).induced.toList, (Generated.hostChunk084[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 6, 0, 4, 2, 5, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 4, 0, 4, 1, 3, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1013]

theorem fixed_values_1014 :
    (fixedDensityCounts (maskGraph 7 384957), fixedComplementCounts (maskGraph 7 384957)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 4, 0, 4, 6, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 4, 4, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_1014_semantics :
    ((Generated.hostChunk084[6]).induced.toList, (Generated.hostChunk084[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[6]).mask)) := by
  have hm : (Generated.hostChunk084[6]).mask = 384957 := by decide +kernel
  have hv : ((Generated.hostChunk084[6]).induced.toList, (Generated.hostChunk084[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 4, 0, 4, 6, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 4, 4, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1014]

theorem fixed_values_1015 :
    (fixedDensityCounts (maskGraph 7 384958), fixedComplementCounts (maskGraph 7 384958)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 4, 6, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 2, 5, 2, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_1015_semantics :
    ((Generated.hostChunk084[7]).induced.toList, (Generated.hostChunk084[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[7]).mask)) := by
  have hm : (Generated.hostChunk084[7]).mask = 384958 := by decide +kernel
  have hv : ((Generated.hostChunk084[7]).induced.toList, (Generated.hostChunk084[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 4, 6, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 2, 5, 2, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1015]

theorem fixed_values_1016 :
    (fixedDensityCounts (maskGraph 7 384959), fixedComplementCounts (maskGraph 7 384959)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 3, 1, 7, 2, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 3, 1, 4, 2, 1, 1]) := by
  decide +kernel

theorem fixed_host_1016_semantics :
    ((Generated.hostChunk084[8]).induced.toList, (Generated.hostChunk084[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[8]).mask)) := by
  have hm : (Generated.hostChunk084[8]).mask = 384959 := by decide +kernel
  have hv : ((Generated.hostChunk084[8]).induced.toList, (Generated.hostChunk084[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 3, 1, 7, 2, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 3, 1, 4, 2, 1, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1016]

theorem fixed_values_1017 :
    (fixedDensityCounts (maskGraph 7 385022), fixedComplementCounts (maskGraph 7 385022)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 4, 2, 4, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 3, 2, 2, 3, 0]) := by
  decide +kernel

theorem fixed_host_1017_semantics :
    ((Generated.hostChunk084[9]).induced.toList, (Generated.hostChunk084[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[9]).mask)) := by
  have hm : (Generated.hostChunk084[9]).mask = 385022 := by decide +kernel
  have hv : ((Generated.hostChunk084[9]).induced.toList, (Generated.hostChunk084[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 4, 2, 4, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 3, 2, 2, 3, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1017]

theorem fixed_values_1018 :
    (fixedDensityCounts (maskGraph 7 385023), fixedComplementCounts (maskGraph 7 385023)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 6, 0, 6, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 5, 0, 4, 1]) := by
  decide +kernel

theorem fixed_host_1018_semantics :
    ((Generated.hostChunk084[10]).induced.toList, (Generated.hostChunk084[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[10]).mask)) := by
  have hm : (Generated.hostChunk084[10]).mask = 385023 := by decide +kernel
  have hv : ((Generated.hostChunk084[10]).induced.toList, (Generated.hostChunk084[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 6, 0, 6, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 4, 0, 5, 0, 4, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1018]

theorem fixed_values_1019 :
    (fixedDensityCounts (maskGraph 7 393149), fixedComplementCounts (maskGraph 7 393149)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 9, 6, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 9, 3, 0, 2, 1]) := by
  decide +kernel

theorem fixed_host_1019_semantics :
    ((Generated.hostChunk084[11]).induced.toList, (Generated.hostChunk084[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk084[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk084[11]).mask)) := by
  have hm : (Generated.hostChunk084[11]).mask = 393149 := by decide +kernel
  have hv : ((Generated.hostChunk084[11]).induced.toList, (Generated.hostChunk084[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 9, 6, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 9, 3, 0, 2, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1019]

theorem fixed_chunk_084_semantics :
    ∀ h ∈ Generated.hostChunk084.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk084.toList = [Generated.hostChunk084[0], Generated.hostChunk084[1], Generated.hostChunk084[2], Generated.hostChunk084[3], Generated.hostChunk084[4], Generated.hostChunk084[5], Generated.hostChunk084[6], Generated.hostChunk084[7], Generated.hostChunk084[8], Generated.hostChunk084[9], Generated.hostChunk084[10], Generated.hostChunk084[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_1008_semantics
  · exact fixed_host_1009_semantics
  · exact fixed_host_1010_semantics
  · exact fixed_host_1011_semantics
  · exact fixed_host_1012_semantics
  · exact fixed_host_1013_semantics
  · exact fixed_host_1014_semantics
  · exact fixed_host_1015_semantics
  · exact fixed_host_1016_semantics
  · exact fixed_host_1017_semantics
  · exact fixed_host_1018_semantics
  · exact fixed_host_1019_semantics

end InducedPentagons.Paper

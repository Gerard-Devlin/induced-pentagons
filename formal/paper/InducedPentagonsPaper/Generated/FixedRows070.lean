import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData070
import InducedPentagonsPaper.Generated.FixedRows062

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0840 :
    (fixedDensityCounts (maskGraph 7 114029), fixedComplementCounts (maskGraph 7 114029)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0840_semantics :
    ((Generated.hostChunk070[0]).induced.toList, (Generated.hostChunk070[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[0]).mask)) := by
  have hm : (Generated.hostChunk070[0]).mask = 114029 := by decide +kernel
  have hv : ((Generated.hostChunk070[0]).induced.toList, (Generated.hostChunk070[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0840]

theorem fixed_values_0841 :
    (fixedDensityCounts (maskGraph 7 114031), fixedComplementCounts (maskGraph 7 114031)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 4, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0841_semantics :
    ((Generated.hostChunk070[1]).induced.toList, (Generated.hostChunk070[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[1]).mask)) := by
  have hm : (Generated.hostChunk070[1]).mask = 114031 := by decide +kernel
  have hv : ((Generated.hostChunk070[1]).induced.toList, (Generated.hostChunk070[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 4, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0841]

theorem fixed_values_0842 :
    (fixedDensityCounts (maskGraph 7 114034), fixedComplementCounts (maskGraph 7 114034)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 2, 1, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0842_semantics :
    ((Generated.hostChunk070[2]).induced.toList, (Generated.hostChunk070[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[2]).mask)) := by
  have hm : (Generated.hostChunk070[2]).mask = 114034 := by decide +kernel
  have hv : ((Generated.hostChunk070[2]).induced.toList, (Generated.hostChunk070[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 2, 1, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0842]

theorem fixed_values_0843 :
    (fixedDensityCounts (maskGraph 7 114035), fixedComplementCounts (maskGraph 7 114035)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 1, 0, 7, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0843_semantics :
    ((Generated.hostChunk070[3]).induced.toList, (Generated.hostChunk070[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[3]).mask)) := by
  have hm : (Generated.hostChunk070[3]).mask = 114035 := by decide +kernel
  have hv : ((Generated.hostChunk070[3]).induced.toList, (Generated.hostChunk070[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 1, 0, 7, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0843]

theorem fixed_values_0844 :
    (fixedDensityCounts (maskGraph 7 114036), fixedComplementCounts (maskGraph 7 114036)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 0, 0, 0, 0, 6, 4, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0844_semantics :
    ((Generated.hostChunk070[4]).induced.toList, (Generated.hostChunk070[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[4]).mask)) := by
  have hm : (Generated.hostChunk070[4]).mask = 114036 := by decide +kernel
  have hv : ((Generated.hostChunk070[4]).induced.toList, (Generated.hostChunk070[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 0, 0, 0, 0, 6, 4, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0844]

theorem fixed_values_0845 :
    (fixedDensityCounts (maskGraph 7 114037), fixedComplementCounts (maskGraph 7 114037)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 5, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0845_semantics :
    ((Generated.hostChunk070[5]).induced.toList, (Generated.hostChunk070[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[5]).mask)) := by
  have hm : (Generated.hostChunk070[5]).mask = 114037 := by decide +kernel
  have hv : ((Generated.hostChunk070[5]).induced.toList, (Generated.hostChunk070[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 5, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0845]

theorem fixed_values_0846 :
    (fixedDensityCounts (maskGraph 7 114038), fixedComplementCounts (maskGraph 7 114038)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 3, 2, 2, 1, 1, 3, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0846_semantics :
    ((Generated.hostChunk070[6]).induced.toList, (Generated.hostChunk070[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[6]).mask)) := by
  have hm : (Generated.hostChunk070[6]).mask = 114038 := by decide +kernel
  have hv : ((Generated.hostChunk070[6]).induced.toList, (Generated.hostChunk070[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 3, 2, 2, 1, 1, 3, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0846]

theorem fixed_values_0847 :
    (fixedDensityCounts (maskGraph 7 114039), fixedComplementCounts (maskGraph 7 114039)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 2, 5, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 3, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0847_semantics :
    ((Generated.hostChunk070[7]).induced.toList, (Generated.hostChunk070[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[7]).mask)) := by
  have hm : (Generated.hostChunk070[7]).mask = 114039 := by decide +kernel
  have hv : ((Generated.hostChunk070[7]).induced.toList, (Generated.hostChunk070[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 2, 5, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 3, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0847]

theorem fixed_values_0848 :
    (fixedDensityCounts (maskGraph 7 114040), fixedComplementCounts (maskGraph 7 114040)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 5, 1, 0, 0, 0, 0, 3, 1, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0848_semantics :
    ((Generated.hostChunk070[8]).induced.toList, (Generated.hostChunk070[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[8]).mask)) := by
  have hm : (Generated.hostChunk070[8]).mask = 114040 := by decide +kernel
  have hv : ((Generated.hostChunk070[8]).induced.toList, (Generated.hostChunk070[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 5, 1, 0, 0, 0, 0, 3, 1, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0848]

theorem fixed_values_0849 :
    (fixedDensityCounts (maskGraph 7 114041), fixedComplementCounts (maskGraph 7 114041)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 5, 2, 0, 0, 0, 3, 3, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0849_semantics :
    ((Generated.hostChunk070[9]).induced.toList, (Generated.hostChunk070[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[9]).mask)) := by
  have hm : (Generated.hostChunk070[9]).mask = 114041 := by decide +kernel
  have hv : ((Generated.hostChunk070[9]).induced.toList, (Generated.hostChunk070[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 5, 2, 0, 0, 0, 3, 3, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0849]

theorem fixed_values_0850 :
    (fixedDensityCounts (maskGraph 7 114042), fixedComplementCounts (maskGraph 7 114042)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 5, 2, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 2, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0850_semantics :
    ((Generated.hostChunk070[10]).induced.toList, (Generated.hostChunk070[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[10]).mask)) := by
  have hm : (Generated.hostChunk070[10]).mask = 114042 := by decide +kernel
  have hv : ((Generated.hostChunk070[10]).induced.toList, (Generated.hostChunk070[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 5, 2, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 2, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0850]

theorem fixed_values_0851 :
    (fixedDensityCounts (maskGraph 7 114043), fixedComplementCounts (maskGraph 7 114043)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 1, 3, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0851_semantics :
    ((Generated.hostChunk070[11]).induced.toList, (Generated.hostChunk070[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk070[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk070[11]).mask)) := by
  have hm : (Generated.hostChunk070[11]).mask = 114043 := by decide +kernel
  have hv : ((Generated.hostChunk070[11]).induced.toList, (Generated.hostChunk070[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 1, 3, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0851]

theorem fixed_chunk_070_semantics :
    ∀ h ∈ Generated.hostChunk070.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk070.toList = [Generated.hostChunk070[0], Generated.hostChunk070[1], Generated.hostChunk070[2], Generated.hostChunk070[3], Generated.hostChunk070[4], Generated.hostChunk070[5], Generated.hostChunk070[6], Generated.hostChunk070[7], Generated.hostChunk070[8], Generated.hostChunk070[9], Generated.hostChunk070[10], Generated.hostChunk070[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0840_semantics
  · exact fixed_host_0841_semantics
  · exact fixed_host_0842_semantics
  · exact fixed_host_0843_semantics
  · exact fixed_host_0844_semantics
  · exact fixed_host_0845_semantics
  · exact fixed_host_0846_semantics
  · exact fixed_host_0847_semantics
  · exact fixed_host_0848_semantics
  · exact fixed_host_0849_semantics
  · exact fixed_host_0850_semantics
  · exact fixed_host_0851_semantics

end InducedPentagons.Paper

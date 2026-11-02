import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData071
import InducedPentagonsPaper.Generated.FixedRows063

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0852 :
    (fixedDensityCounts (maskGraph 7 114044), fixedComplementCounts (maskGraph 7 114044)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 2, 5, 0, 0, 2, 3, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 1, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0852_semantics :
    ((Generated.hostChunk071[0]).induced.toList, (Generated.hostChunk071[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[0]).mask)) := by
  have hm : (Generated.hostChunk071[0]).mask = 114044 := by decide +kernel
  have hv : ((Generated.hostChunk071[0]).induced.toList, (Generated.hostChunk071[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 2, 5, 0, 0, 2, 3, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 1, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0852]

theorem fixed_values_0853 :
    (fixedDensityCounts (maskGraph 7 114045), fixedComplementCounts (maskGraph 7 114045)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 1, 3, 0, 1, 0, 2, 4, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1, 3, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0853_semantics :
    ((Generated.hostChunk071[1]).induced.toList, (Generated.hostChunk071[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[1]).mask)) := by
  have hm : (Generated.hostChunk071[1]).mask = 114045 := by decide +kernel
  have hv : ((Generated.hostChunk071[1]).induced.toList, (Generated.hostChunk071[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 1, 3, 0, 1, 0, 2, 4, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1, 3, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0853]

theorem fixed_values_0854 :
    (fixedDensityCounts (maskGraph 7 114046), fixedComplementCounts (maskGraph 7 114046)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 2, 2, 3, 0, 0, 3, 2, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0854_semantics :
    ((Generated.hostChunk071[2]).induced.toList, (Generated.hostChunk071[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[2]).mask)) := by
  have hm : (Generated.hostChunk071[2]).mask = 114046 := by decide +kernel
  have hv : ((Generated.hostChunk071[2]).induced.toList, (Generated.hostChunk071[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 2, 2, 3, 0, 0, 3, 2, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0854]

theorem fixed_values_0855 :
    (fixedDensityCounts (maskGraph 7 114047), fixedComplementCounts (maskGraph 7 114047)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 5, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 3, 0, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0855_semantics :
    ((Generated.hostChunk071[3]).induced.toList, (Generated.hostChunk071[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[3]).mask)) := by
  have hm : (Generated.hostChunk071[3]).mask = 114047 := by decide +kernel
  have hv : ((Generated.hostChunk071[3]).induced.toList, (Generated.hostChunk071[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 5, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 3, 0, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0855]

theorem fixed_values_0856 :
    (fixedDensityCounts (maskGraph 7 114159), fixedComplementCounts (maskGraph 7 114159)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 6, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0856_semantics :
    ((Generated.hostChunk071[4]).induced.toList, (Generated.hostChunk071[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[4]).mask)) := by
  have hm : (Generated.hostChunk071[4]).mask = 114159 := by decide +kernel
  have hv : ((Generated.hostChunk071[4]).induced.toList, (Generated.hostChunk071[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 6, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0856]

theorem fixed_values_0857 :
    (fixedDensityCounts (maskGraph 7 114166), fixedComplementCounts (maskGraph 7 114166)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 4, 0, 1, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0857_semantics :
    ((Generated.hostChunk071[5]).induced.toList, (Generated.hostChunk071[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[5]).mask)) := by
  have hm : (Generated.hostChunk071[5]).mask = 114166 := by decide +kernel
  have hv : ((Generated.hostChunk071[5]).induced.toList, (Generated.hostChunk071[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 4, 0, 1, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0857]

theorem fixed_values_0858 :
    (fixedDensityCounts (maskGraph 7 114167), fixedComplementCounts (maskGraph 7 114167)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 6, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0858_semantics :
    ((Generated.hostChunk071[6]).induced.toList, (Generated.hostChunk071[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[6]).mask)) := by
  have hm : (Generated.hostChunk071[6]).mask = 114167 := by decide +kernel
  have hv : ((Generated.hostChunk071[6]).induced.toList, (Generated.hostChunk071[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 6, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0858]

theorem fixed_values_0859 :
    (fixedDensityCounts (maskGraph 7 114168), fixedComplementCounts (maskGraph 7 114168)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 0, 0, 3, 2, 2, 0, 2, 4, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 2, 0, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0859_semantics :
    ((Generated.hostChunk071[7]).induced.toList, (Generated.hostChunk071[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[7]).mask)) := by
  have hm : (Generated.hostChunk071[7]).mask = 114168 := by decide +kernel
  have hv : ((Generated.hostChunk071[7]).induced.toList, (Generated.hostChunk071[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 0, 0, 3, 2, 2, 0, 2, 4, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 2, 0, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0859]

theorem fixed_values_0860 :
    (fixedDensityCounts (maskGraph 7 114169), fixedComplementCounts (maskGraph 7 114169)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 2, 2, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 2, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0860_semantics :
    ((Generated.hostChunk071[8]).induced.toList, (Generated.hostChunk071[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[8]).mask)) := by
  have hm : (Generated.hostChunk071[8]).mask = 114169 := by decide +kernel
  have hv : ((Generated.hostChunk071[8]).induced.toList, (Generated.hostChunk071[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 2, 2, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 2, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0860]

theorem fixed_values_0861 :
    (fixedDensityCounts (maskGraph 7 114170), fixedComplementCounts (maskGraph 7 114170)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 3, 1, 0, 1, 4, 2, 1, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 2, 0, 1, 1, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0861_semantics :
    ((Generated.hostChunk071[9]).induced.toList, (Generated.hostChunk071[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[9]).mask)) := by
  have hm : (Generated.hostChunk071[9]).mask = 114170 := by decide +kernel
  have hv : ((Generated.hostChunk071[9]).induced.toList, (Generated.hostChunk071[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 3, 1, 0, 1, 4, 2, 1, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 2, 0, 1, 1, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0861]

theorem fixed_values_0862 :
    (fixedDensityCounts (maskGraph 7 114171), fixedComplementCounts (maskGraph 7 114171)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 3, 1, 0, 0, 1, 3, 1, 3, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0862_semantics :
    ((Generated.hostChunk071[10]).induced.toList, (Generated.hostChunk071[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[10]).mask)) := by
  have hm : (Generated.hostChunk071[10]).mask = 114171 := by decide +kernel
  have hv : ((Generated.hostChunk071[10]).induced.toList, (Generated.hostChunk071[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 3, 1, 0, 0, 1, 3, 1, 3, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0862]

theorem fixed_values_0863 :
    (fixedDensityCounts (maskGraph 7 114174), fixedComplementCounts (maskGraph 7 114174)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 2, 2, 3, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0863_semantics :
    ((Generated.hostChunk071[11]).induced.toList, (Generated.hostChunk071[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk071[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk071[11]).mask)) := by
  have hm : (Generated.hostChunk071[11]).mask = 114174 := by decide +kernel
  have hv : ((Generated.hostChunk071[11]).induced.toList, (Generated.hostChunk071[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 2, 2, 3, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0863]

theorem fixed_chunk_071_semantics :
    ∀ h ∈ Generated.hostChunk071.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk071.toList = [Generated.hostChunk071[0], Generated.hostChunk071[1], Generated.hostChunk071[2], Generated.hostChunk071[3], Generated.hostChunk071[4], Generated.hostChunk071[5], Generated.hostChunk071[6], Generated.hostChunk071[7], Generated.hostChunk071[8], Generated.hostChunk071[9], Generated.hostChunk071[10], Generated.hostChunk071[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0852_semantics
  · exact fixed_host_0853_semantics
  · exact fixed_host_0854_semantics
  · exact fixed_host_0855_semantics
  · exact fixed_host_0856_semantics
  · exact fixed_host_0857_semantics
  · exact fixed_host_0858_semantics
  · exact fixed_host_0859_semantics
  · exact fixed_host_0860_semantics
  · exact fixed_host_0861_semantics
  · exact fixed_host_0862_semantics
  · exact fixed_host_0863_semantics

end InducedPentagons.Paper

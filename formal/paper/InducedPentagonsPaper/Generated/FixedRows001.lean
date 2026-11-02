import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData001

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0012 :
    (fixedDensityCounts (maskGraph 7 77), fixedComplementCounts (maskGraph 7 77)) =
      ([2, 6, 6, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0012_semantics :
    ((Generated.hostChunk001[0]).induced.toList, (Generated.hostChunk001[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[0]).mask)) := by
  have hm : (Generated.hostChunk001[0]).mask = 77 := by decide +kernel
  have hv : ((Generated.hostChunk001[0]).induced.toList, (Generated.hostChunk001[0]).complement.toList) =
      ([2, 6, 6, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0012]

theorem fixed_values_0013 :
    (fixedDensityCounts (maskGraph 7 79), fixedComplementCounts (maskGraph 7 79)) =
      ([2, 4, 5, 4, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0013_semantics :
    ((Generated.hostChunk001[1]).induced.toList, (Generated.hostChunk001[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[1]).mask)) := by
  have hm : (Generated.hostChunk001[1]).mask = 79 := by decide +kernel
  have hv : ((Generated.hostChunk001[1]).induced.toList, (Generated.hostChunk001[1]).complement.toList) =
      ([2, 4, 5, 4, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0013]

theorem fixed_values_0014 :
    (fixedDensityCounts (maskGraph 7 92), fixedComplementCounts (maskGraph 7 92)) =
      ([2, 4, 6, 3, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0014_semantics :
    ((Generated.hostChunk001[2]).induced.toList, (Generated.hostChunk001[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[2]).mask)) := by
  have hm : (Generated.hostChunk001[2]).mask = 92 := by decide +kernel
  have hv : ((Generated.hostChunk001[2]).induced.toList, (Generated.hostChunk001[2]).complement.toList) =
      ([2, 4, 6, 3, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0014]

theorem fixed_values_0015 :
    (fixedDensityCounts (maskGraph 7 93), fixedComplementCounts (maskGraph 7 93)) =
      ([2, 4, 3, 5, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0015_semantics :
    ((Generated.hostChunk001[3]).induced.toList, (Generated.hostChunk001[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[3]).mask)) := by
  have hm : (Generated.hostChunk001[3]).mask = 93 := by decide +kernel
  have hv : ((Generated.hostChunk001[3]).induced.toList, (Generated.hostChunk001[3]).complement.toList) =
      ([2, 4, 3, 5, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0015]

theorem fixed_values_0016 :
    (fixedDensityCounts (maskGraph 7 95), fixedComplementCounts (maskGraph 7 95)) =
      ([2, 4, 0, 7, 2, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0016_semantics :
    ((Generated.hostChunk001[4]).induced.toList, (Generated.hostChunk001[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[4]).mask)) := by
  have hm : (Generated.hostChunk001[4]).mask = 95 := by decide +kernel
  have hv : ((Generated.hostChunk001[4]).induced.toList, (Generated.hostChunk001[4]).complement.toList) =
      ([2, 4, 0, 7, 2, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0016]

theorem fixed_values_0017 :
    (fixedDensityCounts (maskGraph 7 124), fixedComplementCounts (maskGraph 7 124)) =
      ([2, 4, 0, 8, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0017_semantics :
    ((Generated.hostChunk001[5]).induced.toList, (Generated.hostChunk001[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[5]).mask)) := by
  have hm : (Generated.hostChunk001[5]).mask = 124 := by decide +kernel
  have hv : ((Generated.hostChunk001[5]).induced.toList, (Generated.hostChunk001[5]).complement.toList) =
      ([2, 4, 0, 8, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0017]

theorem fixed_values_0018 :
    (fixedDensityCounts (maskGraph 7 125), fixedComplementCounts (maskGraph 7 125)) =
      ([2, 4, 0, 4, 5, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0018_semantics :
    ((Generated.hostChunk001[6]).induced.toList, (Generated.hostChunk001[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[6]).mask)) := by
  have hm : (Generated.hostChunk001[6]).mask = 125 := by decide +kernel
  have hv : ((Generated.hostChunk001[6]).induced.toList, (Generated.hostChunk001[6]).complement.toList) =
      ([2, 4, 0, 4, 5, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0018]

theorem fixed_values_0019 :
    (fixedDensityCounts (maskGraph 7 127), fixedComplementCounts (maskGraph 7 127)) =
      ([2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0019_semantics :
    ((Generated.hostChunk001[7]).induced.toList, (Generated.hostChunk001[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[7]).mask)) := by
  have hm : (Generated.hostChunk001[7]).mask = 127 := by decide +kernel
  have hv : ((Generated.hostChunk001[7]).induced.toList, (Generated.hostChunk001[7]).complement.toList) =
      ([2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0019]

theorem fixed_values_0020 :
    (fixedDensityCounts (maskGraph 7 198), fixedComplementCounts (maskGraph 7 198)) =
      ([2, 4, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0020_semantics :
    ((Generated.hostChunk001[8]).induced.toList, (Generated.hostChunk001[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[8]).mask)) := by
  have hm : (Generated.hostChunk001[8]).mask = 198 := by decide +kernel
  have hv : ((Generated.hostChunk001[8]).induced.toList, (Generated.hostChunk001[8]).complement.toList) =
      ([2, 4, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0020]

theorem fixed_values_0021 :
    (fixedDensityCounts (maskGraph 7 199), fixedComplementCounts (maskGraph 7 199)) =
      ([1, 5, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0021_semantics :
    ((Generated.hostChunk001[9]).induced.toList, (Generated.hostChunk001[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[9]).mask)) := by
  have hm : (Generated.hostChunk001[9]).mask = 199 := by decide +kernel
  have hv : ((Generated.hostChunk001[9]).induced.toList, (Generated.hostChunk001[9]).complement.toList) =
      ([1, 5, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0021]

theorem fixed_values_0022 :
    (fixedDensityCounts (maskGraph 7 202), fixedComplementCounts (maskGraph 7 202)) =
      ([1, 6, 7, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0022_semantics :
    ((Generated.hostChunk001[10]).induced.toList, (Generated.hostChunk001[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[10]).mask)) := by
  have hm : (Generated.hostChunk001[10]).mask = 202 := by decide +kernel
  have hv : ((Generated.hostChunk001[10]).induced.toList, (Generated.hostChunk001[10]).complement.toList) =
      ([1, 6, 7, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0022]

theorem fixed_values_0023 :
    (fixedDensityCounts (maskGraph 7 203), fixedComplementCounts (maskGraph 7 203)) =
      ([1, 4, 8, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0023_semantics :
    ((Generated.hostChunk001[11]).induced.toList, (Generated.hostChunk001[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk001[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk001[11]).mask)) := by
  have hm : (Generated.hostChunk001[11]).mask = 203 := by decide +kernel
  have hv : ((Generated.hostChunk001[11]).induced.toList, (Generated.hostChunk001[11]).complement.toList) =
      ([1, 4, 8, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0023]

theorem fixed_chunk_001_semantics :
    ∀ h ∈ Generated.hostChunk001.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk001.toList = [Generated.hostChunk001[0], Generated.hostChunk001[1], Generated.hostChunk001[2], Generated.hostChunk001[3], Generated.hostChunk001[4], Generated.hostChunk001[5], Generated.hostChunk001[6], Generated.hostChunk001[7], Generated.hostChunk001[8], Generated.hostChunk001[9], Generated.hostChunk001[10], Generated.hostChunk001[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0012_semantics
  · exact fixed_host_0013_semantics
  · exact fixed_host_0014_semantics
  · exact fixed_host_0015_semantics
  · exact fixed_host_0016_semantics
  · exact fixed_host_0017_semantics
  · exact fixed_host_0018_semantics
  · exact fixed_host_0019_semantics
  · exact fixed_host_0020_semantics
  · exact fixed_host_0021_semantics
  · exact fixed_host_0022_semantics
  · exact fixed_host_0023_semantics

end InducedPentagons.Paper

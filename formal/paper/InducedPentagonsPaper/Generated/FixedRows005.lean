import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData005

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0060 :
    (fixedDensityCounts (maskGraph 7 2249), fixedComplementCounts (maskGraph 7 2249)) =
      ([0, 6, 3, 0, 0, 3, 2, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0060_semantics :
    ((Generated.hostChunk005[0]).induced.toList, (Generated.hostChunk005[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[0]).mask)) := by
  have hm : (Generated.hostChunk005[0]).mask = 2249 := by decide +kernel
  have hv : ((Generated.hostChunk005[0]).induced.toList, (Generated.hostChunk005[0]).complement.toList) =
      ([0, 6, 3, 0, 0, 3, 2, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0060]

theorem fixed_values_0061 :
    (fixedDensityCounts (maskGraph 7 2251), fixedComplementCounts (maskGraph 7 2251)) =
      ([0, 4, 4, 0, 0, 4, 0, 4, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0061_semantics :
    ((Generated.hostChunk005[1]).induced.toList, (Generated.hostChunk005[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[1]).mask)) := by
  have hm : (Generated.hostChunk005[1]).mask = 2251 := by decide +kernel
  have hv : ((Generated.hostChunk005[1]).induced.toList, (Generated.hostChunk005[1]).complement.toList) =
      ([0, 4, 4, 0, 0, 4, 0, 4, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0061]

theorem fixed_values_0062 :
    (fixedDensityCounts (maskGraph 7 2255), fixedComplementCounts (maskGraph 7 2255)) =
      ([0, 3, 3, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0062_semantics :
    ((Generated.hostChunk005[2]).induced.toList, (Generated.hostChunk005[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[2]).mask)) := by
  have hm : (Generated.hostChunk005[2]).mask = 2255 := by decide +kernel
  have hv : ((Generated.hostChunk005[2]).induced.toList, (Generated.hostChunk005[2]).complement.toList) =
      ([0, 3, 3, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0062]

theorem fixed_values_0063 :
    (fixedDensityCounts (maskGraph 7 2264), fixedComplementCounts (maskGraph 7 2264)) =
      ([0, 3, 3, 0, 0, 4, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0063_semantics :
    ((Generated.hostChunk005[3]).induced.toList, (Generated.hostChunk005[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[3]).mask)) := by
  have hm : (Generated.hostChunk005[3]).mask = 2264 := by decide +kernel
  have hv : ((Generated.hostChunk005[3]).induced.toList, (Generated.hostChunk005[3]).complement.toList) =
      ([0, 3, 3, 0, 0, 4, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0063]

theorem fixed_values_0064 :
    (fixedDensityCounts (maskGraph 7 2265), fixedComplementCounts (maskGraph 7 2265)) =
      ([0, 3, 2, 1, 0, 3, 2, 4, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0064_semantics :
    ((Generated.hostChunk005[4]).induced.toList, (Generated.hostChunk005[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[4]).mask)) := by
  have hm : (Generated.hostChunk005[4]).mask = 2265 := by decide +kernel
  have hv : ((Generated.hostChunk005[4]).induced.toList, (Generated.hostChunk005[4]).complement.toList) =
      ([0, 3, 2, 1, 0, 3, 2, 4, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0064]

theorem fixed_values_0065 :
    (fixedDensityCounts (maskGraph 7 2267), fixedComplementCounts (maskGraph 7 2267)) =
      ([0, 3, 1, 2, 0, 3, 0, 4, 2, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0065_semantics :
    ((Generated.hostChunk005[5]).induced.toList, (Generated.hostChunk005[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[5]).mask)) := by
  have hm : (Generated.hostChunk005[5]).mask = 2267 := by decide +kernel
  have hv : ((Generated.hostChunk005[5]).induced.toList, (Generated.hostChunk005[5]).complement.toList) =
      ([0, 3, 1, 2, 0, 3, 0, 4, 2, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0065]

theorem fixed_values_0066 :
    (fixedDensityCounts (maskGraph 7 2271), fixedComplementCounts (maskGraph 7 2271)) =
      ([0, 3, 0, 3, 0, 3, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0066_semantics :
    ((Generated.hostChunk005[6]).induced.toList, (Generated.hostChunk005[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[6]).mask)) := by
  have hm : (Generated.hostChunk005[6]).mask = 2271 := by decide +kernel
  have hv : ((Generated.hostChunk005[6]).induced.toList, (Generated.hostChunk005[6]).complement.toList) =
      ([0, 3, 0, 3, 0, 3, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0066]

theorem fixed_values_0067 :
    (fixedDensityCounts (maskGraph 7 2296), fixedComplementCounts (maskGraph 7 2296)) =
      ([0, 3, 0, 3, 0, 3, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0067_semantics :
    ((Generated.hostChunk005[7]).induced.toList, (Generated.hostChunk005[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[7]).mask)) := by
  have hm : (Generated.hostChunk005[7]).mask = 2296 := by decide +kernel
  have hv : ((Generated.hostChunk005[7]).induced.toList, (Generated.hostChunk005[7]).complement.toList) =
      ([0, 3, 0, 3, 0, 3, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0067]

theorem fixed_values_0068 :
    (fixedDensityCounts (maskGraph 7 2297), fixedComplementCounts (maskGraph 7 2297)) =
      ([0, 3, 0, 2, 1, 3, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0068_semantics :
    ((Generated.hostChunk005[8]).induced.toList, (Generated.hostChunk005[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[8]).mask)) := by
  have hm : (Generated.hostChunk005[8]).mask = 2297 := by decide +kernel
  have hv : ((Generated.hostChunk005[8]).induced.toList, (Generated.hostChunk005[8]).complement.toList) =
      ([0, 3, 0, 2, 1, 3, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0068]

theorem fixed_values_0069 :
    (fixedDensityCounts (maskGraph 7 2299), fixedComplementCounts (maskGraph 7 2299)) =
      ([0, 3, 0, 1, 2, 3, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0069_semantics :
    ((Generated.hostChunk005[9]).induced.toList, (Generated.hostChunk005[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[9]).mask)) := by
  have hm : (Generated.hostChunk005[9]).mask = 2299 := by decide +kernel
  have hv : ((Generated.hostChunk005[9]).induced.toList, (Generated.hostChunk005[9]).complement.toList) =
      ([0, 3, 0, 1, 2, 3, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0069]

theorem fixed_values_0070 :
    (fixedDensityCounts (maskGraph 7 2303), fixedComplementCounts (maskGraph 7 2303)) =
      ([0, 3, 0, 0, 3, 3, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0070_semantics :
    ((Generated.hostChunk005[10]).induced.toList, (Generated.hostChunk005[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[10]).mask)) := by
  have hm : (Generated.hostChunk005[10]).mask = 2303 := by decide +kernel
  have hv : ((Generated.hostChunk005[10]).induced.toList, (Generated.hostChunk005[10]).complement.toList) =
      ([0, 3, 0, 0, 3, 3, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0070]

theorem fixed_values_0071 :
    (fixedDensityCounts (maskGraph 7 2319), fixedComplementCounts (maskGraph 7 2319)) =
      ([0, 4, 4, 0, 0, 2, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0071_semantics :
    ((Generated.hostChunk005[11]).induced.toList, (Generated.hostChunk005[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk005[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk005[11]).mask)) := by
  have hm : (Generated.hostChunk005[11]).mask = 2319 := by decide +kernel
  have hv : ((Generated.hostChunk005[11]).induced.toList, (Generated.hostChunk005[11]).complement.toList) =
      ([0, 4, 4, 0, 0, 2, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0071]

theorem fixed_chunk_005_semantics :
    ∀ h ∈ Generated.hostChunk005.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk005.toList = [Generated.hostChunk005[0], Generated.hostChunk005[1], Generated.hostChunk005[2], Generated.hostChunk005[3], Generated.hostChunk005[4], Generated.hostChunk005[5], Generated.hostChunk005[6], Generated.hostChunk005[7], Generated.hostChunk005[8], Generated.hostChunk005[9], Generated.hostChunk005[10], Generated.hostChunk005[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0060_semantics
  · exact fixed_host_0061_semantics
  · exact fixed_host_0062_semantics
  · exact fixed_host_0063_semantics
  · exact fixed_host_0064_semantics
  · exact fixed_host_0065_semantics
  · exact fixed_host_0066_semantics
  · exact fixed_host_0067_semantics
  · exact fixed_host_0068_semantics
  · exact fixed_host_0069_semantics
  · exact fixed_host_0070_semantics
  · exact fixed_host_0071_semantics

end InducedPentagons.Paper

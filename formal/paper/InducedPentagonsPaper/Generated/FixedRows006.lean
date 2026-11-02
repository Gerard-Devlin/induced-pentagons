import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData006

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0072 :
    (fixedDensityCounts (maskGraph 7 2320), fixedComplementCounts (maskGraph 7 2320)) =
      ([0, 12, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0072_semantics :
    ((Generated.hostChunk006[0]).induced.toList, (Generated.hostChunk006[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[0]).mask)) := by
  have hm : (Generated.hostChunk006[0]).mask = 2320 := by decide +kernel
  have hv : ((Generated.hostChunk006[0]).induced.toList, (Generated.hostChunk006[0]).complement.toList) =
      ([0, 12, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0072]

theorem fixed_values_0073 :
    (fixedDensityCounts (maskGraph 7 2321), fixedComplementCounts (maskGraph 7 2321)) =
      ([0, 7, 4, 0, 0, 0, 5, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0073_semantics :
    ((Generated.hostChunk006[1]).induced.toList, (Generated.hostChunk006[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[1]).mask)) := by
  have hm : (Generated.hostChunk006[1]).mask = 2321 := by decide +kernel
  have hv : ((Generated.hostChunk006[1]).induced.toList, (Generated.hostChunk006[1]).complement.toList) =
      ([0, 7, 4, 0, 0, 0, 5, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0073]

theorem fixed_values_0074 :
    (fixedDensityCounts (maskGraph 7 2323), fixedComplementCounts (maskGraph 7 2323)) =
      ([0, 5, 4, 1, 0, 0, 2, 6, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0074_semantics :
    ((Generated.hostChunk006[2]).induced.toList, (Generated.hostChunk006[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[2]).mask)) := by
  have hm : (Generated.hostChunk006[2]).mask = 2323 := by decide +kernel
  have hv : ((Generated.hostChunk006[2]).induced.toList, (Generated.hostChunk006[2]).complement.toList) =
      ([0, 5, 4, 1, 0, 0, 2, 6, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0074]

theorem fixed_values_0075 :
    (fixedDensityCounts (maskGraph 7 2326), fixedComplementCounts (maskGraph 7 2326)) =
      ([0, 4, 4, 0, 0, 2, 5, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0075_semantics :
    ((Generated.hostChunk006[3]).induced.toList, (Generated.hostChunk006[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[3]).mask)) := by
  have hm : (Generated.hostChunk006[3]).mask = 2326 := by decide +kernel
  have hv : ((Generated.hostChunk006[3]).induced.toList, (Generated.hostChunk006[3]).complement.toList) =
      ([0, 4, 4, 0, 0, 2, 5, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0075]

theorem fixed_values_0076 :
    (fixedDensityCounts (maskGraph 7 2327), fixedComplementCounts (maskGraph 7 2327)) =
      ([0, 4, 2, 2, 0, 1, 2, 3, 3, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0076_semantics :
    ((Generated.hostChunk006[4]).induced.toList, (Generated.hostChunk006[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[4]).mask)) := by
  have hm : (Generated.hostChunk006[4]).mask = 2327 := by decide +kernel
  have hv : ((Generated.hostChunk006[4]).induced.toList, (Generated.hostChunk006[4]).complement.toList) =
      ([0, 4, 2, 2, 0, 1, 2, 3, 3, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0076]

theorem fixed_values_0077 :
    (fixedDensityCounts (maskGraph 7 2335), fixedComplementCounts (maskGraph 7 2335)) =
      ([0, 4, 0, 4, 0, 0, 2, 0, 6, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0077_semantics :
    ((Generated.hostChunk006[5]).induced.toList, (Generated.hostChunk006[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[5]).mask)) := by
  have hm : (Generated.hostChunk006[5]).mask = 2335 := by decide +kernel
  have hv : ((Generated.hostChunk006[5]).induced.toList, (Generated.hostChunk006[5]).complement.toList) =
      ([0, 4, 0, 4, 0, 0, 2, 0, 6, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0077]

theorem fixed_values_0078 :
    (fixedDensityCounts (maskGraph 7 2352), fixedComplementCounts (maskGraph 7 2352)) =
      ([0, 4, 4, 0, 0, 0, 11, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0078_semantics :
    ((Generated.hostChunk006[6]).induced.toList, (Generated.hostChunk006[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[6]).mask)) := by
  have hm : (Generated.hostChunk006[6]).mask = 2352 := by decide +kernel
  have hv : ((Generated.hostChunk006[6]).induced.toList, (Generated.hostChunk006[6]).complement.toList) =
      ([0, 4, 4, 0, 0, 0, 11, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0078]

theorem fixed_values_0079 :
    (fixedDensityCounts (maskGraph 7 2353), fixedComplementCounts (maskGraph 7 2353)) =
      ([0, 4, 2, 2, 0, 0, 4, 4, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0079_semantics :
    ((Generated.hostChunk006[7]).induced.toList, (Generated.hostChunk006[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[7]).mask)) := by
  have hm : (Generated.hostChunk006[7]).mask = 2353 := by decide +kernel
  have hv : ((Generated.hostChunk006[7]).induced.toList, (Generated.hostChunk006[7]).complement.toList) =
      ([0, 4, 2, 2, 0, 0, 4, 4, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0079]

theorem fixed_values_0080 :
    (fixedDensityCounts (maskGraph 7 2355), fixedComplementCounts (maskGraph 7 2355)) =
      ([0, 4, 1, 2, 1, 0, 2, 4, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0080_semantics :
    ((Generated.hostChunk006[8]).induced.toList, (Generated.hostChunk006[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[8]).mask)) := by
  have hm : (Generated.hostChunk006[8]).mask = 2355 := by decide +kernel
  have hv : ((Generated.hostChunk006[8]).induced.toList, (Generated.hostChunk006[8]).complement.toList) =
      ([0, 4, 1, 2, 1, 0, 2, 4, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0080]

theorem fixed_values_0081 :
    (fixedDensityCounts (maskGraph 7 2358), fixedComplementCounts (maskGraph 7 2358)) =
      ([0, 4, 0, 4, 0, 0, 2, 0, 4, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0081_semantics :
    ((Generated.hostChunk006[9]).induced.toList, (Generated.hostChunk006[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[9]).mask)) := by
  have hm : (Generated.hostChunk006[9]).mask = 2358 := by decide +kernel
  have hv : ((Generated.hostChunk006[9]).induced.toList, (Generated.hostChunk006[9]).complement.toList) =
      ([0, 4, 0, 4, 0, 0, 2, 0, 4, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0081]

theorem fixed_values_0082 :
    (fixedDensityCounts (maskGraph 7 2359), fixedComplementCounts (maskGraph 7 2359)) =
      ([0, 4, 0, 2, 2, 0, 2, 0, 2, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0082_semantics :
    ((Generated.hostChunk006[10]).induced.toList, (Generated.hostChunk006[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[10]).mask)) := by
  have hm : (Generated.hostChunk006[10]).mask = 2359 := by decide +kernel
  have hv : ((Generated.hostChunk006[10]).induced.toList, (Generated.hostChunk006[10]).complement.toList) =
      ([0, 4, 0, 2, 2, 0, 2, 0, 2, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0082]

theorem fixed_values_0083 :
    (fixedDensityCounts (maskGraph 7 2367), fixedComplementCounts (maskGraph 7 2367)) =
      ([0, 4, 0, 0, 4, 0, 2, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0083_semantics :
    ((Generated.hostChunk006[11]).induced.toList, (Generated.hostChunk006[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk006[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk006[11]).mask)) := by
  have hm : (Generated.hostChunk006[11]).mask = 2367 := by decide +kernel
  have hv : ((Generated.hostChunk006[11]).induced.toList, (Generated.hostChunk006[11]).complement.toList) =
      ([0, 4, 0, 0, 4, 0, 2, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0083]

theorem fixed_chunk_006_semantics :
    ∀ h ∈ Generated.hostChunk006.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk006.toList = [Generated.hostChunk006[0], Generated.hostChunk006[1], Generated.hostChunk006[2], Generated.hostChunk006[3], Generated.hostChunk006[4], Generated.hostChunk006[5], Generated.hostChunk006[6], Generated.hostChunk006[7], Generated.hostChunk006[8], Generated.hostChunk006[9], Generated.hostChunk006[10], Generated.hostChunk006[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0072_semantics
  · exact fixed_host_0073_semantics
  · exact fixed_host_0074_semantics
  · exact fixed_host_0075_semantics
  · exact fixed_host_0076_semantics
  · exact fixed_host_0077_semantics
  · exact fixed_host_0078_semantics
  · exact fixed_host_0079_semantics
  · exact fixed_host_0080_semantics
  · exact fixed_host_0081_semantics
  · exact fixed_host_0082_semantics
  · exact fixed_host_0083_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData029
import InducedPentagonsPaper.Generated.FixedRows021

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0348 :
    (fixedDensityCounts (maskGraph 7 15871), fixedComplementCounts (maskGraph 7 15871)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0348_semantics :
    ((Generated.hostChunk029[0]).induced.toList, (Generated.hostChunk029[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[0]).mask)) := by
  have hm : (Generated.hostChunk029[0]).mask = 15871 := by decide +kernel
  have hv : ((Generated.hostChunk029[0]).induced.toList, (Generated.hostChunk029[0]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0348]

theorem fixed_values_0349 :
    (fixedDensityCounts (maskGraph 7 16316), fixedComplementCounts (maskGraph 7 16316)) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0349_semantics :
    ((Generated.hostChunk029[1]).induced.toList, (Generated.hostChunk029[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[1]).mask)) := by
  have hm : (Generated.hostChunk029[1]).mask = 16316 := by decide +kernel
  have hv : ((Generated.hostChunk029[1]).induced.toList, (Generated.hostChunk029[1]).complement.toList) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0349]

theorem fixed_values_0350 :
    (fixedDensityCounts (maskGraph 7 16317), fixedComplementCounts (maskGraph 7 16317)) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0350_semantics :
    ((Generated.hostChunk029[2]).induced.toList, (Generated.hostChunk029[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[2]).mask)) := by
  have hm : (Generated.hostChunk029[2]).mask = 16317 := by decide +kernel
  have hv : ((Generated.hostChunk029[2]).induced.toList, (Generated.hostChunk029[2]).complement.toList) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0350]

theorem fixed_values_0351 :
    (fixedDensityCounts (maskGraph 7 16318), fixedComplementCounts (maskGraph 7 16318)) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 5, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0351_semantics :
    ((Generated.hostChunk029[3]).induced.toList, (Generated.hostChunk029[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[3]).mask)) := by
  have hm : (Generated.hostChunk029[3]).mask = 16318 := by decide +kernel
  have hv : ((Generated.hostChunk029[3]).induced.toList, (Generated.hostChunk029[3]).complement.toList) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 5, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0351]

theorem fixed_values_0352 :
    (fixedDensityCounts (maskGraph 7 16319), fixedComplementCounts (maskGraph 7 16319)) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0352_semantics :
    ((Generated.hostChunk029[4]).induced.toList, (Generated.hostChunk029[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[4]).mask)) := by
  have hm : (Generated.hostChunk029[4]).mask = 16319 := by decide +kernel
  have hv : ((Generated.hostChunk029[4]).induced.toList, (Generated.hostChunk029[4]).complement.toList) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0352]

theorem fixed_values_0353 :
    (fixedDensityCounts (maskGraph 7 16382), fixedComplementCounts (maskGraph 7 16382)) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0353_semantics :
    ((Generated.hostChunk029[5]).induced.toList, (Generated.hostChunk029[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[5]).mask)) := by
  have hm : (Generated.hostChunk029[5]).mask = 16382 := by decide +kernel
  have hv : ((Generated.hostChunk029[5]).induced.toList, (Generated.hostChunk029[5]).complement.toList) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0353]

theorem fixed_values_0354 :
    (fixedDensityCounts (maskGraph 7 16383), fixedComplementCounts (maskGraph 7 16383)) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0354_semantics :
    ((Generated.hostChunk029[6]).induced.toList, (Generated.hostChunk029[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[6]).mask)) := by
  have hm : (Generated.hostChunk029[6]).mask = 16383 := by decide +kernel
  have hv : ((Generated.hostChunk029[6]).induced.toList, (Generated.hostChunk029[6]).complement.toList) =
      ([0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0354]

theorem fixed_values_0355 :
    (fixedDensityCounts (maskGraph 7 32700), fixedComplementCounts (maskGraph 7 32700)) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0355_semantics :
    ((Generated.hostChunk029[7]).induced.toList, (Generated.hostChunk029[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[7]).mask)) := by
  have hm : (Generated.hostChunk029[7]).mask = 32700 := by decide +kernel
  have hv : ((Generated.hostChunk029[7]).induced.toList, (Generated.hostChunk029[7]).complement.toList) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0355]

theorem fixed_values_0356 :
    (fixedDensityCounts (maskGraph 7 32701), fixedComplementCounts (maskGraph 7 32701)) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0356_semantics :
    ((Generated.hostChunk029[8]).induced.toList, (Generated.hostChunk029[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[8]).mask)) := by
  have hm : (Generated.hostChunk029[8]).mask = 32701 := by decide +kernel
  have hv : ((Generated.hostChunk029[8]).induced.toList, (Generated.hostChunk029[8]).complement.toList) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0356]

theorem fixed_values_0357 :
    (fixedDensityCounts (maskGraph 7 32703), fixedComplementCounts (maskGraph 7 32703)) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0357_semantics :
    ((Generated.hostChunk029[9]).induced.toList, (Generated.hostChunk029[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[9]).mask)) := by
  have hm : (Generated.hostChunk029[9]).mask = 32703 := by decide +kernel
  have hv : ((Generated.hostChunk029[9]).induced.toList, (Generated.hostChunk029[9]).complement.toList) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0357]

theorem fixed_values_0358 :
    (fixedDensityCounts (maskGraph 7 32767), fixedComplementCounts (maskGraph 7 32767)) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0358_semantics :
    ((Generated.hostChunk029[10]).induced.toList, (Generated.hostChunk029[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[10]).mask)) := by
  have hm : (Generated.hostChunk029[10]).mask = 32767 := by decide +kernel
  have hv : ((Generated.hostChunk029[10]).induced.toList, (Generated.hostChunk029[10]).complement.toList) =
      ([0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0358]

theorem fixed_values_0359 :
    (fixedDensityCounts (maskGraph 7 39375), fixedComplementCounts (maskGraph 7 39375)) =
      ([0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0359_semantics :
    ((Generated.hostChunk029[11]).induced.toList, (Generated.hostChunk029[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk029[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk029[11]).mask)) := by
  have hm : (Generated.hostChunk029[11]).mask = 39375 := by decide +kernel
  have hv : ((Generated.hostChunk029[11]).induced.toList, (Generated.hostChunk029[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0359]

theorem fixed_chunk_029_semantics :
    ∀ h ∈ Generated.hostChunk029.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk029.toList = [Generated.hostChunk029[0], Generated.hostChunk029[1], Generated.hostChunk029[2], Generated.hostChunk029[3], Generated.hostChunk029[4], Generated.hostChunk029[5], Generated.hostChunk029[6], Generated.hostChunk029[7], Generated.hostChunk029[8], Generated.hostChunk029[9], Generated.hostChunk029[10], Generated.hostChunk029[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0348_semantics
  · exact fixed_host_0349_semantics
  · exact fixed_host_0350_semantics
  · exact fixed_host_0351_semantics
  · exact fixed_host_0352_semantics
  · exact fixed_host_0353_semantics
  · exact fixed_host_0354_semantics
  · exact fixed_host_0355_semantics
  · exact fixed_host_0356_semantics
  · exact fixed_host_0357_semantics
  · exact fixed_host_0358_semantics
  · exact fixed_host_0359_semantics

end InducedPentagons.Paper

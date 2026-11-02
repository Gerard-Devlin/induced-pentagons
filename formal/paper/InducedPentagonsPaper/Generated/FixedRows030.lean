import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData030
import InducedPentagonsPaper.Generated.FixedRows022

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0360 :
    (fixedDensityCounts (maskGraph 7 39376), fixedComplementCounts (maskGraph 7 39376)) =
      ([0, 0, 0, 0, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0360_semantics :
    ((Generated.hostChunk030[0]).induced.toList, (Generated.hostChunk030[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[0]).mask)) := by
  have hm : (Generated.hostChunk030[0]).mask = 39376 := by decide +kernel
  have hv : ((Generated.hostChunk030[0]).induced.toList, (Generated.hostChunk030[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0360]

theorem fixed_values_0361 :
    (fixedDensityCounts (maskGraph 7 39377), fixedComplementCounts (maskGraph 7 39377)) =
      ([0, 0, 0, 0, 0, 5, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0361_semantics :
    ((Generated.hostChunk030[1]).induced.toList, (Generated.hostChunk030[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[1]).mask)) := by
  have hm : (Generated.hostChunk030[1]).mask = 39377 := by decide +kernel
  have hv : ((Generated.hostChunk030[1]).induced.toList, (Generated.hostChunk030[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 5, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0361]

theorem fixed_values_0362 :
    (fixedDensityCounts (maskGraph 7 39379), fixedComplementCounts (maskGraph 7 39379)) =
      ([0, 0, 0, 0, 0, 4, 1, 4, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0362_semantics :
    ((Generated.hostChunk030[2]).induced.toList, (Generated.hostChunk030[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[2]).mask)) := by
  have hm : (Generated.hostChunk030[2]).mask = 39379 := by decide +kernel
  have hv : ((Generated.hostChunk030[2]).induced.toList, (Generated.hostChunk030[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 1, 4, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0362]

theorem fixed_values_0363 :
    (fixedDensityCounts (maskGraph 7 39383), fixedComplementCounts (maskGraph 7 39383)) =
      ([0, 0, 0, 0, 0, 4, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 3, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0363_semantics :
    ((Generated.hostChunk030[3]).induced.toList, (Generated.hostChunk030[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[3]).mask)) := by
  have hm : (Generated.hostChunk030[3]).mask = 39383 := by decide +kernel
  have hv : ((Generated.hostChunk030[3]).induced.toList, (Generated.hostChunk030[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 3, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0363]

theorem fixed_values_0364 :
    (fixedDensityCounts (maskGraph 7 39391), fixedComplementCounts (maskGraph 7 39391)) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0364_semantics :
    ((Generated.hostChunk030[4]).induced.toList, (Generated.hostChunk030[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[4]).mask)) := by
  have hm : (Generated.hostChunk030[4]).mask = 39391 := by decide +kernel
  have hv : ((Generated.hostChunk030[4]).induced.toList, (Generated.hostChunk030[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0364]

theorem fixed_values_0365 :
    (fixedDensityCounts (maskGraph 7 39408), fixedComplementCounts (maskGraph 7 39408)) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0365_semantics :
    ((Generated.hostChunk030[5]).induced.toList, (Generated.hostChunk030[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[5]).mask)) := by
  have hm : (Generated.hostChunk030[5]).mask = 39408 := by decide +kernel
  have hv : ((Generated.hostChunk030[5]).induced.toList, (Generated.hostChunk030[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0365]

theorem fixed_values_0366 :
    (fixedDensityCounts (maskGraph 7 39409), fixedComplementCounts (maskGraph 7 39409)) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0366_semantics :
    ((Generated.hostChunk030[6]).induced.toList, (Generated.hostChunk030[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[6]).mask)) := by
  have hm : (Generated.hostChunk030[6]).mask = 39409 := by decide +kernel
  have hv : ((Generated.hostChunk030[6]).induced.toList, (Generated.hostChunk030[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0366]

theorem fixed_values_0367 :
    (fixedDensityCounts (maskGraph 7 39411), fixedComplementCounts (maskGraph 7 39411)) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0367_semantics :
    ((Generated.hostChunk030[7]).induced.toList, (Generated.hostChunk030[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[7]).mask)) := by
  have hm : (Generated.hostChunk030[7]).mask = 39411 := by decide +kernel
  have hv : ((Generated.hostChunk030[7]).induced.toList, (Generated.hostChunk030[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0367]

theorem fixed_values_0368 :
    (fixedDensityCounts (maskGraph 7 39415), fixedComplementCounts (maskGraph 7 39415)) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0368_semantics :
    ((Generated.hostChunk030[8]).induced.toList, (Generated.hostChunk030[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[8]).mask)) := by
  have hm : (Generated.hostChunk030[8]).mask = 39415 := by decide +kernel
  have hv : ((Generated.hostChunk030[8]).induced.toList, (Generated.hostChunk030[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0368]

theorem fixed_values_0369 :
    (fixedDensityCounts (maskGraph 7 39423), fixedComplementCounts (maskGraph 7 39423)) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0369_semantics :
    ((Generated.hostChunk030[9]).induced.toList, (Generated.hostChunk030[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[9]).mask)) := by
  have hm : (Generated.hostChunk030[9]).mask = 39423 := by decide +kernel
  have hv : ((Generated.hostChunk030[9]).induced.toList, (Generated.hostChunk030[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0369]

theorem fixed_values_0370 :
    (fixedDensityCounts (maskGraph 7 39441), fixedComplementCounts (maskGraph 7 39441)) =
      ([0, 0, 0, 0, 0, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0370_semantics :
    ((Generated.hostChunk030[10]).induced.toList, (Generated.hostChunk030[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[10]).mask)) := by
  have hm : (Generated.hostChunk030[10]).mask = 39441 := by decide +kernel
  have hv : ((Generated.hostChunk030[10]).induced.toList, (Generated.hostChunk030[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0370]

theorem fixed_values_0371 :
    (fixedDensityCounts (maskGraph 7 39443), fixedComplementCounts (maskGraph 7 39443)) =
      ([0, 0, 0, 0, 0, 4, 5, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 4, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0371_semantics :
    ((Generated.hostChunk030[11]).induced.toList, (Generated.hostChunk030[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk030[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk030[11]).mask)) := by
  have hm : (Generated.hostChunk030[11]).mask = 39443 := by decide +kernel
  have hv : ((Generated.hostChunk030[11]).induced.toList, (Generated.hostChunk030[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 5, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 4, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0371]

theorem fixed_chunk_030_semantics :
    ∀ h ∈ Generated.hostChunk030.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk030.toList = [Generated.hostChunk030[0], Generated.hostChunk030[1], Generated.hostChunk030[2], Generated.hostChunk030[3], Generated.hostChunk030[4], Generated.hostChunk030[5], Generated.hostChunk030[6], Generated.hostChunk030[7], Generated.hostChunk030[8], Generated.hostChunk030[9], Generated.hostChunk030[10], Generated.hostChunk030[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0360_semantics
  · exact fixed_host_0361_semantics
  · exact fixed_host_0362_semantics
  · exact fixed_host_0363_semantics
  · exact fixed_host_0364_semantics
  · exact fixed_host_0365_semantics
  · exact fixed_host_0366_semantics
  · exact fixed_host_0367_semantics
  · exact fixed_host_0368_semantics
  · exact fixed_host_0369_semantics
  · exact fixed_host_0370_semantics
  · exact fixed_host_0371_semantics

end InducedPentagons.Paper

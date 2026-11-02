import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData038
import InducedPentagonsPaper.Generated.FixedRows030

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0456 :
    (fixedDensityCounts (maskGraph 7 40511), fixedComplementCounts (maskGraph 7 40511)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0456_semantics :
    ((Generated.hostChunk038[0]).induced.toList, (Generated.hostChunk038[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[0]).mask)) := by
  have hm : (Generated.hostChunk038[0]).mask = 40511 := by decide +kernel
  have hv : ((Generated.hostChunk038[0]).induced.toList, (Generated.hostChunk038[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0456]

theorem fixed_values_0457 :
    (fixedDensityCounts (maskGraph 7 40562), fixedComplementCounts (maskGraph 7 40562)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 4, 1, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0457_semantics :
    ((Generated.hostChunk038[1]).induced.toList, (Generated.hostChunk038[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[1]).mask)) := by
  have hm : (Generated.hostChunk038[1]).mask = 40562 := by decide +kernel
  have hv : ((Generated.hostChunk038[1]).induced.toList, (Generated.hostChunk038[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 4, 1, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0457]

theorem fixed_values_0458 :
    (fixedDensityCounts (maskGraph 7 40563), fixedComplementCounts (maskGraph 7 40563)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 4, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0458_semantics :
    ((Generated.hostChunk038[2]).induced.toList, (Generated.hostChunk038[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[2]).mask)) := by
  have hm : (Generated.hostChunk038[2]).mask = 40563 := by decide +kernel
  have hv : ((Generated.hostChunk038[2]).induced.toList, (Generated.hostChunk038[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 4, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0458]

theorem fixed_values_0459 :
    (fixedDensityCounts (maskGraph 7 40564), fixedComplementCounts (maskGraph 7 40564)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 1, 0, 4, 1, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0459_semantics :
    ((Generated.hostChunk038[3]).induced.toList, (Generated.hostChunk038[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[3]).mask)) := by
  have hm : (Generated.hostChunk038[3]).mask = 40564 := by decide +kernel
  have hv : ((Generated.hostChunk038[3]).induced.toList, (Generated.hostChunk038[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 1, 0, 4, 1, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0459]

theorem fixed_values_0460 :
    (fixedDensityCounts (maskGraph 7 40565), fixedComplementCounts (maskGraph 7 40565)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 8, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0460_semantics :
    ((Generated.hostChunk038[4]).induced.toList, (Generated.hostChunk038[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[4]).mask)) := by
  have hm : (Generated.hostChunk038[4]).mask = 40565 := by decide +kernel
  have hv : ((Generated.hostChunk038[4]).induced.toList, (Generated.hostChunk038[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 8, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0460]

theorem fixed_values_0461 :
    (fixedDensityCounts (maskGraph 7 40566), fixedComplementCounts (maskGraph 7 40566)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 1, 0, 2, 0, 3, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0461_semantics :
    ((Generated.hostChunk038[5]).induced.toList, (Generated.hostChunk038[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[5]).mask)) := by
  have hm : (Generated.hostChunk038[5]).mask = 40566 := by decide +kernel
  have hv : ((Generated.hostChunk038[5]).induced.toList, (Generated.hostChunk038[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 1, 0, 2, 0, 3, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0461]

theorem fixed_values_0462 :
    (fixedDensityCounts (maskGraph 7 40567), fixedComplementCounts (maskGraph 7 40567)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 4, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0462_semantics :
    ((Generated.hostChunk038[6]).induced.toList, (Generated.hostChunk038[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[6]).mask)) := by
  have hm : (Generated.hostChunk038[6]).mask = 40567 := by decide +kernel
  have hv : ((Generated.hostChunk038[6]).induced.toList, (Generated.hostChunk038[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 4, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0462]

theorem fixed_values_0463 :
    (fixedDensityCounts (maskGraph 7 40572), fixedComplementCounts (maskGraph 7 40572)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0463_semantics :
    ((Generated.hostChunk038[7]).induced.toList, (Generated.hostChunk038[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[7]).mask)) := by
  have hm : (Generated.hostChunk038[7]).mask = 40572 := by decide +kernel
  have hv : ((Generated.hostChunk038[7]).induced.toList, (Generated.hostChunk038[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0463]

theorem fixed_values_0464 :
    (fixedDensityCounts (maskGraph 7 40573), fixedComplementCounts (maskGraph 7 40573)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0464_semantics :
    ((Generated.hostChunk038[8]).induced.toList, (Generated.hostChunk038[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[8]).mask)) := by
  have hm : (Generated.hostChunk038[8]).mask = 40573 := by decide +kernel
  have hv : ((Generated.hostChunk038[8]).induced.toList, (Generated.hostChunk038[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0464]

theorem fixed_values_0465 :
    (fixedDensityCounts (maskGraph 7 40574), fixedComplementCounts (maskGraph 7 40574)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0465_semantics :
    ((Generated.hostChunk038[9]).induced.toList, (Generated.hostChunk038[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[9]).mask)) := by
  have hm : (Generated.hostChunk038[9]).mask = 40574 := by decide +kernel
  have hv : ((Generated.hostChunk038[9]).induced.toList, (Generated.hostChunk038[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0465]

theorem fixed_values_0466 :
    (fixedDensityCounts (maskGraph 7 40575), fixedComplementCounts (maskGraph 7 40575)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 4, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0466_semantics :
    ((Generated.hostChunk038[10]).induced.toList, (Generated.hostChunk038[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[10]).mask)) := by
  have hm : (Generated.hostChunk038[10]).mask = 40575 := by decide +kernel
  have hv : ((Generated.hostChunk038[10]).induced.toList, (Generated.hostChunk038[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 4, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0466]

theorem fixed_values_0467 :
    (fixedDensityCounts (maskGraph 7 40694), fixedComplementCounts (maskGraph 7 40694)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 1, 0, 0, 0, 4, 0, 2, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0467_semantics :
    ((Generated.hostChunk038[11]).induced.toList, (Generated.hostChunk038[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk038[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk038[11]).mask)) := by
  have hm : (Generated.hostChunk038[11]).mask = 40694 := by decide +kernel
  have hv : ((Generated.hostChunk038[11]).induced.toList, (Generated.hostChunk038[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 1, 0, 0, 0, 4, 0, 2, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0467]

theorem fixed_chunk_038_semantics :
    ∀ h ∈ Generated.hostChunk038.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk038.toList = [Generated.hostChunk038[0], Generated.hostChunk038[1], Generated.hostChunk038[2], Generated.hostChunk038[3], Generated.hostChunk038[4], Generated.hostChunk038[5], Generated.hostChunk038[6], Generated.hostChunk038[7], Generated.hostChunk038[8], Generated.hostChunk038[9], Generated.hostChunk038[10], Generated.hostChunk038[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0456_semantics
  · exact fixed_host_0457_semantics
  · exact fixed_host_0458_semantics
  · exact fixed_host_0459_semantics
  · exact fixed_host_0460_semantics
  · exact fixed_host_0461_semantics
  · exact fixed_host_0462_semantics
  · exact fixed_host_0463_semantics
  · exact fixed_host_0464_semantics
  · exact fixed_host_0465_semantics
  · exact fixed_host_0466_semantics
  · exact fixed_host_0467_semantics

end InducedPentagons.Paper

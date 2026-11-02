import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData065
import InducedPentagonsPaper.Generated.FixedRows057

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0780 :
    (fixedDensityCounts (maskGraph 7 61373), fixedComplementCounts (maskGraph 7 61373)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 2, 1, 0, 0, 4, 0, 3, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0780_semantics :
    ((Generated.hostChunk065[0]).induced.toList, (Generated.hostChunk065[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[0]).mask)) := by
  have hm : (Generated.hostChunk065[0]).mask = 61373 := by decide +kernel
  have hv : ((Generated.hostChunk065[0]).induced.toList, (Generated.hostChunk065[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 2, 1, 0, 0, 4, 0, 3, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0780]

theorem fixed_values_0781 :
    (fixedDensityCounts (maskGraph 7 61374), fixedComplementCounts (maskGraph 7 61374)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 4, 3, 5, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0781_semantics :
    ((Generated.hostChunk065[1]).induced.toList, (Generated.hostChunk065[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[1]).mask)) := by
  have hm : (Generated.hostChunk065[1]).mask = 61374 := by decide +kernel
  have hv : ((Generated.hostChunk065[1]).induced.toList, (Generated.hostChunk065[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 4, 3, 5, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0781]

theorem fixed_values_0782 :
    (fixedDensityCounts (maskGraph 7 61375), fixedComplementCounts (maskGraph 7 61375)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 3, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0782_semantics :
    ((Generated.hostChunk065[2]).induced.toList, (Generated.hostChunk065[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[2]).mask)) := by
  have hm : (Generated.hostChunk065[2]).mask = 61375 := by decide +kernel
  have hv : ((Generated.hostChunk065[2]).induced.toList, (Generated.hostChunk065[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 3, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0782]

theorem fixed_values_0783 :
    (fixedDensityCounts (maskGraph 7 61438), fixedComplementCounts (maskGraph 7 61438)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0783_semantics :
    ((Generated.hostChunk065[3]).induced.toList, (Generated.hostChunk065[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[3]).mask)) := by
  have hm : (Generated.hostChunk065[3]).mask = 61438 := by decide +kernel
  have hv : ((Generated.hostChunk065[3]).induced.toList, (Generated.hostChunk065[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0783]

theorem fixed_values_0784 :
    (fixedDensityCounts (maskGraph 7 61439), fixedComplementCounts (maskGraph 7 61439)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0784_semantics :
    ((Generated.hostChunk065[4]).induced.toList, (Generated.hostChunk065[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[4]).mask)) := by
  have hm : (Generated.hostChunk065[4]).mask = 61439 := by decide +kernel
  have hv : ((Generated.hostChunk065[4]).induced.toList, (Generated.hostChunk065[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0784]

theorem fixed_values_0785 :
    (fixedDensityCounts (maskGraph 7 65468), fixedComplementCounts (maskGraph 7 65468)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 11, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0785_semantics :
    ((Generated.hostChunk065[5]).induced.toList, (Generated.hostChunk065[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[5]).mask)) := by
  have hm : (Generated.hostChunk065[5]).mask = 65468 := by decide +kernel
  have hv : ((Generated.hostChunk065[5]).induced.toList, (Generated.hostChunk065[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 11, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0785]

theorem fixed_values_0786 :
    (fixedDensityCounts (maskGraph 7 65469), fixedComplementCounts (maskGraph 7 65469)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0786_semantics :
    ((Generated.hostChunk065[6]).induced.toList, (Generated.hostChunk065[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[6]).mask)) := by
  have hm : (Generated.hostChunk065[6]).mask = 65469 := by decide +kernel
  have hv : ((Generated.hostChunk065[6]).induced.toList, (Generated.hostChunk065[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0786]

theorem fixed_values_0787 :
    (fixedDensityCounts (maskGraph 7 65471), fixedComplementCounts (maskGraph 7 65471)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 5, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0787_semantics :
    ((Generated.hostChunk065[7]).induced.toList, (Generated.hostChunk065[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[7]).mask)) := by
  have hm : (Generated.hostChunk065[7]).mask = 65471 := by decide +kernel
  have hv : ((Generated.hostChunk065[7]).induced.toList, (Generated.hostChunk065[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 5, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0787]

theorem fixed_values_0788 :
    (fixedDensityCounts (maskGraph 7 65535), fixedComplementCounts (maskGraph 7 65535)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0788_semantics :
    ((Generated.hostChunk065[8]).induced.toList, (Generated.hostChunk065[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[8]).mask)) := by
  have hm : (Generated.hostChunk065[8]).mask = 65535 := by decide +kernel
  have hv : ((Generated.hostChunk065[8]).induced.toList, (Generated.hostChunk065[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0788]

theorem fixed_values_0789 :
    (fixedDensityCounts (maskGraph 7 111582), fixedComplementCounts (maskGraph 7 111582)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0789_semantics :
    ((Generated.hostChunk065[9]).induced.toList, (Generated.hostChunk065[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[9]).mask)) := by
  have hm : (Generated.hostChunk065[9]).mask = 111582 := by decide +kernel
  have hv : ((Generated.hostChunk065[9]).induced.toList, (Generated.hostChunk065[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0789]

theorem fixed_values_0790 :
    (fixedDensityCounts (maskGraph 7 111583), fixedComplementCounts (maskGraph 7 111583)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0790_semantics :
    ((Generated.hostChunk065[10]).induced.toList, (Generated.hostChunk065[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[10]).mask)) := by
  have hm : (Generated.hostChunk065[10]).mask = 111583 := by decide +kernel
  have hv : ((Generated.hostChunk065[10]).induced.toList, (Generated.hostChunk065[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0790]

theorem fixed_values_0791 :
    (fixedDensityCounts (maskGraph 7 111594), fixedComplementCounts (maskGraph 7 111594)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 2, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0791_semantics :
    ((Generated.hostChunk065[11]).induced.toList, (Generated.hostChunk065[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk065[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk065[11]).mask)) := by
  have hm : (Generated.hostChunk065[11]).mask = 111594 := by decide +kernel
  have hv : ((Generated.hostChunk065[11]).induced.toList, (Generated.hostChunk065[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 2, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0791]

theorem fixed_chunk_065_semantics :
    ∀ h ∈ Generated.hostChunk065.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk065.toList = [Generated.hostChunk065[0], Generated.hostChunk065[1], Generated.hostChunk065[2], Generated.hostChunk065[3], Generated.hostChunk065[4], Generated.hostChunk065[5], Generated.hostChunk065[6], Generated.hostChunk065[7], Generated.hostChunk065[8], Generated.hostChunk065[9], Generated.hostChunk065[10], Generated.hostChunk065[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0780_semantics
  · exact fixed_host_0781_semantics
  · exact fixed_host_0782_semantics
  · exact fixed_host_0783_semantics
  · exact fixed_host_0784_semantics
  · exact fixed_host_0785_semantics
  · exact fixed_host_0786_semantics
  · exact fixed_host_0787_semantics
  · exact fixed_host_0788_semantics
  · exact fixed_host_0789_semantics
  · exact fixed_host_0790_semantics
  · exact fixed_host_0791_semantics

end InducedPentagons.Paper

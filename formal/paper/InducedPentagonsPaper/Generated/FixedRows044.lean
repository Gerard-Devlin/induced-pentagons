import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData044
import InducedPentagonsPaper.Generated.FixedRows036

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0528 :
    (fixedDensityCounts (maskGraph 7 42495), fixedComplementCounts (maskGraph 7 42495)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 5, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 3, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0528_semantics :
    ((Generated.hostChunk044[0]).induced.toList, (Generated.hostChunk044[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[0]).mask)) := by
  have hm : (Generated.hostChunk044[0]).mask = 42495 := by decide +kernel
  have hv : ((Generated.hostChunk044[0]).induced.toList, (Generated.hostChunk044[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 5, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 3, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0528]

theorem fixed_values_0529 :
    (fixedDensityCounts (maskGraph 7 43006), fixedComplementCounts (maskGraph 7 43006)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0529_semantics :
    ((Generated.hostChunk044[1]).induced.toList, (Generated.hostChunk044[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[1]).mask)) := by
  have hm : (Generated.hostChunk044[1]).mask = 43006 := by decide +kernel
  have hv : ((Generated.hostChunk044[1]).induced.toList, (Generated.hostChunk044[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0529]

theorem fixed_values_0530 :
    (fixedDensityCounts (maskGraph 7 43007), fixedComplementCounts (maskGraph 7 43007)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 6, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0530_semantics :
    ((Generated.hostChunk044[2]).induced.toList, (Generated.hostChunk044[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[2]).mask)) := by
  have hm : (Generated.hostChunk044[2]).mask = 43007 := by decide +kernel
  have hv : ((Generated.hostChunk044[2]).induced.toList, (Generated.hostChunk044[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 6, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0530]

theorem fixed_values_0531 :
    (fixedDensityCounts (maskGraph 7 43807), fixedComplementCounts (maskGraph 7 43807)) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0531_semantics :
    ((Generated.hostChunk044[3]).induced.toList, (Generated.hostChunk044[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[3]).mask)) := by
  have hm : (Generated.hostChunk044[3]).mask = 43807 := by decide +kernel
  have hv : ((Generated.hostChunk044[3]).induced.toList, (Generated.hostChunk044[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0531]

theorem fixed_values_0532 :
    (fixedDensityCounts (maskGraph 7 43814), fixedComplementCounts (maskGraph 7 43814)) =
      ([0, 0, 0, 0, 0, 0, 0, 7, 1, 3, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0532_semantics :
    ((Generated.hostChunk044[4]).induced.toList, (Generated.hostChunk044[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[4]).mask)) := by
  have hm : (Generated.hostChunk044[4]).mask = 43814 := by decide +kernel
  have hv : ((Generated.hostChunk044[4]).induced.toList, (Generated.hostChunk044[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 7, 1, 3, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0532]

theorem fixed_values_0533 :
    (fixedDensityCounts (maskGraph 7 43815), fixedComplementCounts (maskGraph 7 43815)) =
      ([0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 3, 1, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0533_semantics :
    ((Generated.hostChunk044[5]).induced.toList, (Generated.hostChunk044[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[5]).mask)) := by
  have hm : (Generated.hostChunk044[5]).mask = 43815 := by decide +kernel
  have hv : ((Generated.hostChunk044[5]).induced.toList, (Generated.hostChunk044[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 3, 1, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0533]

theorem fixed_values_0534 :
    (fixedDensityCounts (maskGraph 7 43821), fixedComplementCounts (maskGraph 7 43821)) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 2, 1, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0534_semantics :
    ((Generated.hostChunk044[6]).induced.toList, (Generated.hostChunk044[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[6]).mask)) := by
  have hm : (Generated.hostChunk044[6]).mask = 43821 := by decide +kernel
  have hv : ((Generated.hostChunk044[6]).induced.toList, (Generated.hostChunk044[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 2, 1, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0534]

theorem fixed_values_0535 :
    (fixedDensityCounts (maskGraph 7 43823), fixedComplementCounts (maskGraph 7 43823)) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 2, 2, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0535_semantics :
    ((Generated.hostChunk044[7]).induced.toList, (Generated.hostChunk044[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[7]).mask)) := by
  have hm : (Generated.hostChunk044[7]).mask = 43823 := by decide +kernel
  have hv : ((Generated.hostChunk044[7]).induced.toList, (Generated.hostChunk044[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 2, 2, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0535]

theorem fixed_values_0536 :
    (fixedDensityCounts (maskGraph 7 43839), fixedComplementCounts (maskGraph 7 43839)) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0536_semantics :
    ((Generated.hostChunk044[8]).induced.toList, (Generated.hostChunk044[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[8]).mask)) := by
  have hm : (Generated.hostChunk044[8]).mask = 43839 := by decide +kernel
  have hv : ((Generated.hostChunk044[8]).induced.toList, (Generated.hostChunk044[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0536]

theorem fixed_values_0537 :
    (fixedDensityCounts (maskGraph 7 43868), fixedComplementCounts (maskGraph 7 43868)) =
      ([0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0537_semantics :
    ((Generated.hostChunk044[9]).induced.toList, (Generated.hostChunk044[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[9]).mask)) := by
  have hm : (Generated.hostChunk044[9]).mask = 43868 := by decide +kernel
  have hv : ((Generated.hostChunk044[9]).induced.toList, (Generated.hostChunk044[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0537]

theorem fixed_values_0538 :
    (fixedDensityCounts (maskGraph 7 43869), fixedComplementCounts (maskGraph 7 43869)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0538_semantics :
    ((Generated.hostChunk044[10]).induced.toList, (Generated.hostChunk044[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[10]).mask)) := by
  have hm : (Generated.hostChunk044[10]).mask = 43869 := by decide +kernel
  have hv : ((Generated.hostChunk044[10]).induced.toList, (Generated.hostChunk044[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0538]

theorem fixed_values_0539 :
    (fixedDensityCounts (maskGraph 7 43871), fixedComplementCounts (maskGraph 7 43871)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0539_semantics :
    ((Generated.hostChunk044[11]).induced.toList, (Generated.hostChunk044[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk044[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk044[11]).mask)) := by
  have hm : (Generated.hostChunk044[11]).mask = 43871 := by decide +kernel
  have hv : ((Generated.hostChunk044[11]).induced.toList, (Generated.hostChunk044[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0539]

theorem fixed_chunk_044_semantics :
    ∀ h ∈ Generated.hostChunk044.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk044.toList = [Generated.hostChunk044[0], Generated.hostChunk044[1], Generated.hostChunk044[2], Generated.hostChunk044[3], Generated.hostChunk044[4], Generated.hostChunk044[5], Generated.hostChunk044[6], Generated.hostChunk044[7], Generated.hostChunk044[8], Generated.hostChunk044[9], Generated.hostChunk044[10], Generated.hostChunk044[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0528_semantics
  · exact fixed_host_0529_semantics
  · exact fixed_host_0530_semantics
  · exact fixed_host_0531_semantics
  · exact fixed_host_0532_semantics
  · exact fixed_host_0533_semantics
  · exact fixed_host_0534_semantics
  · exact fixed_host_0535_semantics
  · exact fixed_host_0536_semantics
  · exact fixed_host_0537_semantics
  · exact fixed_host_0538_semantics
  · exact fixed_host_0539_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData034
import InducedPentagonsPaper.Generated.FixedRows026

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0408 :
    (fixedDensityCounts (maskGraph 7 39542), fixedComplementCounts (maskGraph 7 39542)) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 1, 0, 4, 1, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0408_semantics :
    ((Generated.hostChunk034[0]).induced.toList, (Generated.hostChunk034[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[0]).mask)) := by
  have hm : (Generated.hostChunk034[0]).mask = 39542 := by decide +kernel
  have hv : ((Generated.hostChunk034[0]).induced.toList, (Generated.hostChunk034[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 1, 0, 4, 1, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0408]

theorem fixed_values_0409 :
    (fixedDensityCounts (maskGraph 7 39543), fixedComplementCounts (maskGraph 7 39543)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 3, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0409_semantics :
    ((Generated.hostChunk034[1]).induced.toList, (Generated.hostChunk034[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[1]).mask)) := by
  have hm : (Generated.hostChunk034[1]).mask = 39543 := by decide +kernel
  have hv : ((Generated.hostChunk034[1]).induced.toList, (Generated.hostChunk034[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 3, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0409]

theorem fixed_values_0410 :
    (fixedDensityCounts (maskGraph 7 39548), fixedComplementCounts (maskGraph 7 39548)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 4, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0410_semantics :
    ((Generated.hostChunk034[2]).induced.toList, (Generated.hostChunk034[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[2]).mask)) := by
  have hm : (Generated.hostChunk034[2]).mask = 39548 := by decide +kernel
  have hv : ((Generated.hostChunk034[2]).induced.toList, (Generated.hostChunk034[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 4, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0410]

theorem fixed_values_0411 :
    (fixedDensityCounts (maskGraph 7 39549), fixedComplementCounts (maskGraph 7 39549)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 2, 4, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0411_semantics :
    ((Generated.hostChunk034[3]).induced.toList, (Generated.hostChunk034[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[3]).mask)) := by
  have hm : (Generated.hostChunk034[3]).mask = 39549 := by decide +kernel
  have hv : ((Generated.hostChunk034[3]).induced.toList, (Generated.hostChunk034[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 2, 4, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0411]

theorem fixed_values_0412 :
    (fixedDensityCounts (maskGraph 7 39550), fixedComplementCounts (maskGraph 7 39550)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 2, 3, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0412_semantics :
    ((Generated.hostChunk034[4]).induced.toList, (Generated.hostChunk034[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[4]).mask)) := by
  have hm : (Generated.hostChunk034[4]).mask = 39550 := by decide +kernel
  have hv : ((Generated.hostChunk034[4]).induced.toList, (Generated.hostChunk034[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 2, 3, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0412]

theorem fixed_values_0413 :
    (fixedDensityCounts (maskGraph 7 39551), fixedComplementCounts (maskGraph 7 39551)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0413_semantics :
    ((Generated.hostChunk034[5]).induced.toList, (Generated.hostChunk034[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[5]).mask)) := by
  have hm : (Generated.hostChunk034[5]).mask = 39551 := by decide +kernel
  have hv : ((Generated.hostChunk034[5]).induced.toList, (Generated.hostChunk034[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0413]

theorem fixed_values_0414 :
    (fixedDensityCounts (maskGraph 7 39639), fixedComplementCounts (maskGraph 7 39639)) =
      ([0, 0, 0, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0414_semantics :
    ((Generated.hostChunk034[6]).induced.toList, (Generated.hostChunk034[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[6]).mask)) := by
  have hm : (Generated.hostChunk034[6]).mask = 39639 := by decide +kernel
  have hv : ((Generated.hostChunk034[6]).induced.toList, (Generated.hostChunk034[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0414]

theorem fixed_values_0415 :
    (fixedDensityCounts (maskGraph 7 39642), fixedComplementCounts (maskGraph 7 39642)) =
      ([0, 0, 0, 0, 0, 1, 0, 7, 4, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0415_semantics :
    ((Generated.hostChunk034[7]).induced.toList, (Generated.hostChunk034[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[7]).mask)) := by
  have hm : (Generated.hostChunk034[7]).mask = 39642 := by decide +kernel
  have hv : ((Generated.hostChunk034[7]).induced.toList, (Generated.hostChunk034[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 7, 4, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0415]

theorem fixed_values_0416 :
    (fixedDensityCounts (maskGraph 7 39643), fixedComplementCounts (maskGraph 7 39643)) =
      ([0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0416_semantics :
    ((Generated.hostChunk034[8]).induced.toList, (Generated.hostChunk034[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[8]).mask)) := by
  have hm : (Generated.hostChunk034[8]).mask = 39643 := by decide +kernel
  have hv : ((Generated.hostChunk034[8]).induced.toList, (Generated.hostChunk034[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0416]

theorem fixed_values_0417 :
    (fixedDensityCounts (maskGraph 7 39646), fixedComplementCounts (maskGraph 7 39646)) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 6, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0417_semantics :
    ((Generated.hostChunk034[9]).induced.toList, (Generated.hostChunk034[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[9]).mask)) := by
  have hm : (Generated.hostChunk034[9]).mask = 39646 := by decide +kernel
  have hv : ((Generated.hostChunk034[9]).induced.toList, (Generated.hostChunk034[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 6, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0417]

theorem fixed_values_0418 :
    (fixedDensityCounts (maskGraph 7 39647), fixedComplementCounts (maskGraph 7 39647)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 5, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0418_semantics :
    ((Generated.hostChunk034[10]).induced.toList, (Generated.hostChunk034[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[10]).mask)) := by
  have hm : (Generated.hostChunk034[10]).mask = 39647 := by decide +kernel
  have hv : ((Generated.hostChunk034[10]).induced.toList, (Generated.hostChunk034[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 5, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0418]

theorem fixed_values_0419 :
    (fixedDensityCounts (maskGraph 7 39654), fixedComplementCounts (maskGraph 7 39654)) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 2, 0, 4, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0419_semantics :
    ((Generated.hostChunk034[11]).induced.toList, (Generated.hostChunk034[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk034[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk034[11]).mask)) := by
  have hm : (Generated.hostChunk034[11]).mask = 39654 := by decide +kernel
  have hv : ((Generated.hostChunk034[11]).induced.toList, (Generated.hostChunk034[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 2, 0, 4, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0419]

theorem fixed_chunk_034_semantics :
    ∀ h ∈ Generated.hostChunk034.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk034.toList = [Generated.hostChunk034[0], Generated.hostChunk034[1], Generated.hostChunk034[2], Generated.hostChunk034[3], Generated.hostChunk034[4], Generated.hostChunk034[5], Generated.hostChunk034[6], Generated.hostChunk034[7], Generated.hostChunk034[8], Generated.hostChunk034[9], Generated.hostChunk034[10], Generated.hostChunk034[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0408_semantics
  · exact fixed_host_0409_semantics
  · exact fixed_host_0410_semantics
  · exact fixed_host_0411_semantics
  · exact fixed_host_0412_semantics
  · exact fixed_host_0413_semantics
  · exact fixed_host_0414_semantics
  · exact fixed_host_0415_semantics
  · exact fixed_host_0416_semantics
  · exact fixed_host_0417_semantics
  · exact fixed_host_0418_semantics
  · exact fixed_host_0419_semantics

end InducedPentagons.Paper

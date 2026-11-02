import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData031
import InducedPentagonsPaper.Generated.FixedRows023

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0372 :
    (fixedDensityCounts (maskGraph 7 39447), fixedComplementCounts (maskGraph 7 39447)) =
      ([0, 0, 0, 0, 0, 3, 3, 4, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 3, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0372_semantics :
    ((Generated.hostChunk031[0]).induced.toList, (Generated.hostChunk031[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[0]).mask)) := by
  have hm : (Generated.hostChunk031[0]).mask = 39447 := by decide +kernel
  have hv : ((Generated.hostChunk031[0]).induced.toList, (Generated.hostChunk031[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 3, 3, 4, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 3, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0372]

theorem fixed_values_0373 :
    (fixedDensityCounts (maskGraph 7 39455), fixedComplementCounts (maskGraph 7 39455)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0373_semantics :
    ((Generated.hostChunk031[1]).induced.toList, (Generated.hostChunk031[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[1]).mask)) := by
  have hm : (Generated.hostChunk031[1]).mask = 39455 := by decide +kernel
  have hv : ((Generated.hostChunk031[1]).induced.toList, (Generated.hostChunk031[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0373]

theorem fixed_values_0374 :
    (fixedDensityCounts (maskGraph 7 39456), fixedComplementCounts (maskGraph 7 39456)) =
      ([0, 0, 0, 0, 0, 4, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0374_semantics :
    ((Generated.hostChunk031[2]).induced.toList, (Generated.hostChunk031[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[2]).mask)) := by
  have hm : (Generated.hostChunk031[2]).mask = 39456 := by decide +kernel
  have hv : ((Generated.hostChunk031[2]).induced.toList, (Generated.hostChunk031[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 4, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0374]

theorem fixed_values_0375 :
    (fixedDensityCounts (maskGraph 7 39457), fixedComplementCounts (maskGraph 7 39457)) =
      ([0, 0, 0, 0, 0, 3, 6, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0375_semantics :
    ((Generated.hostChunk031[3]).induced.toList, (Generated.hostChunk031[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[3]).mask)) := by
  have hm : (Generated.hostChunk031[3]).mask = 39457 := by decide +kernel
  have hv : ((Generated.hostChunk031[3]).induced.toList, (Generated.hostChunk031[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 3, 6, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0375]

theorem fixed_values_0376 :
    (fixedDensityCounts (maskGraph 7 39458), fixedComplementCounts (maskGraph 7 39458)) =
      ([0, 0, 0, 0, 0, 2, 8, 4, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0376_semantics :
    ((Generated.hostChunk031[4]).induced.toList, (Generated.hostChunk031[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[4]).mask)) := by
  have hm : (Generated.hostChunk031[4]).mask = 39458 := by decide +kernel
  have hv : ((Generated.hostChunk031[4]).induced.toList, (Generated.hostChunk031[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 8, 4, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0376]

theorem fixed_values_0377 :
    (fixedDensityCounts (maskGraph 7 39459), fixedComplementCounts (maskGraph 7 39459)) =
      ([0, 0, 0, 0, 0, 2, 4, 4, 1, 2, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0377_semantics :
    ((Generated.hostChunk031[5]).induced.toList, (Generated.hostChunk031[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[5]).mask)) := by
  have hm : (Generated.hostChunk031[5]).mask = 39459 := by decide +kernel
  have hv : ((Generated.hostChunk031[5]).induced.toList, (Generated.hostChunk031[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 4, 4, 1, 2, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0377]

theorem fixed_values_0378 :
    (fixedDensityCounts (maskGraph 7 39462), fixedComplementCounts (maskGraph 7 39462)) =
      ([0, 0, 0, 0, 0, 2, 4, 4, 2, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0378_semantics :
    ((Generated.hostChunk031[6]).induced.toList, (Generated.hostChunk031[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[6]).mask)) := by
  have hm : (Generated.hostChunk031[6]).mask = 39462 := by decide +kernel
  have hv : ((Generated.hostChunk031[6]).induced.toList, (Generated.hostChunk031[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 4, 4, 2, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0378]

theorem fixed_values_0379 :
    (fixedDensityCounts (maskGraph 7 39463), fixedComplementCounts (maskGraph 7 39463)) =
      ([0, 0, 0, 0, 0, 2, 3, 3, 1, 0, 4, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0379_semantics :
    ((Generated.hostChunk031[7]).induced.toList, (Generated.hostChunk031[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[7]).mask)) := by
  have hm : (Generated.hostChunk031[7]).mask = 39463 := by decide +kernel
  have hv : ((Generated.hostChunk031[7]).induced.toList, (Generated.hostChunk031[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 3, 1, 0, 4, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0379]

theorem fixed_values_0380 :
    (fixedDensityCounts (maskGraph 7 39470), fixedComplementCounts (maskGraph 7 39470)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0380_semantics :
    ((Generated.hostChunk031[8]).induced.toList, (Generated.hostChunk031[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[8]).mask)) := by
  have hm : (Generated.hostChunk031[8]).mask = 39470 := by decide +kernel
  have hv : ((Generated.hostChunk031[8]).induced.toList, (Generated.hostChunk031[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0380]

theorem fixed_values_0381 :
    (fixedDensityCounts (maskGraph 7 39471), fixedComplementCounts (maskGraph 7 39471)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 3, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0381_semantics :
    ((Generated.hostChunk031[9]).induced.toList, (Generated.hostChunk031[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[9]).mask)) := by
  have hm : (Generated.hostChunk031[9]).mask = 39471 := by decide +kernel
  have hv : ((Generated.hostChunk031[9]).induced.toList, (Generated.hostChunk031[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 3, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0381]

theorem fixed_values_0382 :
    (fixedDensityCounts (maskGraph 7 39473), fixedComplementCounts (maskGraph 7 39473)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0382_semantics :
    ((Generated.hostChunk031[10]).induced.toList, (Generated.hostChunk031[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[10]).mask)) := by
  have hm : (Generated.hostChunk031[10]).mask = 39473 := by decide +kernel
  have hv : ((Generated.hostChunk031[10]).induced.toList, (Generated.hostChunk031[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0382]

theorem fixed_values_0383 :
    (fixedDensityCounts (maskGraph 7 39475), fixedComplementCounts (maskGraph 7 39475)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 2, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0383_semantics :
    ((Generated.hostChunk031[11]).induced.toList, (Generated.hostChunk031[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk031[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk031[11]).mask)) := by
  have hm : (Generated.hostChunk031[11]).mask = 39475 := by decide +kernel
  have hv : ((Generated.hostChunk031[11]).induced.toList, (Generated.hostChunk031[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 2, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0383]

theorem fixed_chunk_031_semantics :
    ∀ h ∈ Generated.hostChunk031.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk031.toList = [Generated.hostChunk031[0], Generated.hostChunk031[1], Generated.hostChunk031[2], Generated.hostChunk031[3], Generated.hostChunk031[4], Generated.hostChunk031[5], Generated.hostChunk031[6], Generated.hostChunk031[7], Generated.hostChunk031[8], Generated.hostChunk031[9], Generated.hostChunk031[10], Generated.hostChunk031[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0372_semantics
  · exact fixed_host_0373_semantics
  · exact fixed_host_0374_semantics
  · exact fixed_host_0375_semantics
  · exact fixed_host_0376_semantics
  · exact fixed_host_0377_semantics
  · exact fixed_host_0378_semantics
  · exact fixed_host_0379_semantics
  · exact fixed_host_0380_semantics
  · exact fixed_host_0381_semantics
  · exact fixed_host_0382_semantics
  · exact fixed_host_0383_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData028
import InducedPentagonsPaper.Generated.FixedRows020

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0336 :
    (fixedDensityCounts (maskGraph 7 15356), fixedComplementCounts (maskGraph 7 15356)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0336_semantics :
    ((Generated.hostChunk028[0]).induced.toList, (Generated.hostChunk028[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[0]).mask)) := by
  have hm : (Generated.hostChunk028[0]).mask = 15356 := by decide +kernel
  have hv : ((Generated.hostChunk028[0]).induced.toList, (Generated.hostChunk028[0]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0336]

theorem fixed_values_0337 :
    (fixedDensityCounts (maskGraph 7 15357), fixedComplementCounts (maskGraph 7 15357)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0337_semantics :
    ((Generated.hostChunk028[1]).induced.toList, (Generated.hostChunk028[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[1]).mask)) := by
  have hm : (Generated.hostChunk028[1]).mask = 15357 := by decide +kernel
  have hv : ((Generated.hostChunk028[1]).induced.toList, (Generated.hostChunk028[1]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0337]

theorem fixed_values_0338 :
    (fixedDensityCounts (maskGraph 7 15359), fixedComplementCounts (maskGraph 7 15359)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0338_semantics :
    ((Generated.hostChunk028[2]).induced.toList, (Generated.hostChunk028[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[2]).mask)) := by
  have hm : (Generated.hostChunk028[2]).mask = 15359 := by decide +kernel
  have hv : ((Generated.hostChunk028[2]).induced.toList, (Generated.hostChunk028[2]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0338]

theorem fixed_values_0339 :
    (fixedDensityCounts (maskGraph 7 15796), fixedComplementCounts (maskGraph 7 15796)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0339_semantics :
    ((Generated.hostChunk028[3]).induced.toList, (Generated.hostChunk028[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[3]).mask)) := by
  have hm : (Generated.hostChunk028[3]).mask = 15796 := by decide +kernel
  have hv : ((Generated.hostChunk028[3]).induced.toList, (Generated.hostChunk028[3]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0339]

theorem fixed_values_0340 :
    (fixedDensityCounts (maskGraph 7 15797), fixedComplementCounts (maskGraph 7 15797)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0340_semantics :
    ((Generated.hostChunk028[4]).induced.toList, (Generated.hostChunk028[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[4]).mask)) := by
  have hm : (Generated.hostChunk028[4]).mask = 15797 := by decide +kernel
  have hv : ((Generated.hostChunk028[4]).induced.toList, (Generated.hostChunk028[4]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0340]

theorem fixed_values_0341 :
    (fixedDensityCounts (maskGraph 7 15799), fixedComplementCounts (maskGraph 7 15799)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 2, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0341_semantics :
    ((Generated.hostChunk028[5]).induced.toList, (Generated.hostChunk028[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[5]).mask)) := by
  have hm : (Generated.hostChunk028[5]).mask = 15799 := by decide +kernel
  have hv : ((Generated.hostChunk028[5]).induced.toList, (Generated.hostChunk028[5]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 2, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0341]

theorem fixed_values_0342 :
    (fixedDensityCounts (maskGraph 7 15804), fixedComplementCounts (maskGraph 7 15804)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 12, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0342_semantics :
    ((Generated.hostChunk028[6]).induced.toList, (Generated.hostChunk028[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[6]).mask)) := by
  have hm : (Generated.hostChunk028[6]).mask = 15804 := by decide +kernel
  have hv : ((Generated.hostChunk028[6]).induced.toList, (Generated.hostChunk028[6]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 12, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0342]

theorem fixed_values_0343 :
    (fixedDensityCounts (maskGraph 7 15805), fixedComplementCounts (maskGraph 7 15805)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 5, 3, 1, 1, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0343_semantics :
    ((Generated.hostChunk028[7]).induced.toList, (Generated.hostChunk028[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[7]).mask)) := by
  have hm : (Generated.hostChunk028[7]).mask = 15805 := by decide +kernel
  have hv : ((Generated.hostChunk028[7]).induced.toList, (Generated.hostChunk028[7]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 5, 3, 1, 1, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0343]

theorem fixed_values_0344 :
    (fixedDensityCounts (maskGraph 7 15807), fixedComplementCounts (maskGraph 7 15807)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 6, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0344_semantics :
    ((Generated.hostChunk028[8]).induced.toList, (Generated.hostChunk028[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[8]).mask)) := by
  have hm : (Generated.hostChunk028[8]).mask = 15807 := by decide +kernel
  have hv : ((Generated.hostChunk028[8]).induced.toList, (Generated.hostChunk028[8]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 6, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0344]

theorem fixed_values_0345 :
    (fixedDensityCounts (maskGraph 7 15863), fixedComplementCounts (maskGraph 7 15863)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0345_semantics :
    ((Generated.hostChunk028[9]).induced.toList, (Generated.hostChunk028[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[9]).mask)) := by
  have hm : (Generated.hostChunk028[9]).mask = 15863 := by decide +kernel
  have hv : ((Generated.hostChunk028[9]).induced.toList, (Generated.hostChunk028[9]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0345]

theorem fixed_values_0346 :
    (fixedDensityCounts (maskGraph 7 15868), fixedComplementCounts (maskGraph 7 15868)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0346_semantics :
    ((Generated.hostChunk028[10]).induced.toList, (Generated.hostChunk028[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[10]).mask)) := by
  have hm : (Generated.hostChunk028[10]).mask = 15868 := by decide +kernel
  have hv : ((Generated.hostChunk028[10]).induced.toList, (Generated.hostChunk028[10]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0346]

theorem fixed_values_0347 :
    (fixedDensityCounts (maskGraph 7 15869), fixedComplementCounts (maskGraph 7 15869)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 5, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0347_semantics :
    ((Generated.hostChunk028[11]).induced.toList, (Generated.hostChunk028[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk028[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk028[11]).mask)) := by
  have hm : (Generated.hostChunk028[11]).mask = 15869 := by decide +kernel
  have hv : ((Generated.hostChunk028[11]).induced.toList, (Generated.hostChunk028[11]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 5, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0347]

theorem fixed_chunk_028_semantics :
    ∀ h ∈ Generated.hostChunk028.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk028.toList = [Generated.hostChunk028[0], Generated.hostChunk028[1], Generated.hostChunk028[2], Generated.hostChunk028[3], Generated.hostChunk028[4], Generated.hostChunk028[5], Generated.hostChunk028[6], Generated.hostChunk028[7], Generated.hostChunk028[8], Generated.hostChunk028[9], Generated.hostChunk028[10], Generated.hostChunk028[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0336_semantics
  · exact fixed_host_0337_semantics
  · exact fixed_host_0338_semantics
  · exact fixed_host_0339_semantics
  · exact fixed_host_0340_semantics
  · exact fixed_host_0341_semantics
  · exact fixed_host_0342_semantics
  · exact fixed_host_0343_semantics
  · exact fixed_host_0344_semantics
  · exact fixed_host_0345_semantics
  · exact fixed_host_0346_semantics
  · exact fixed_host_0347_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData039
import InducedPentagonsPaper.Generated.FixedRows031

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0468 :
    (fixedDensityCounts (maskGraph 7 40695), fixedComplementCounts (maskGraph 7 40695)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0468_semantics :
    ((Generated.hostChunk039[0]).induced.toList, (Generated.hostChunk039[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[0]).mask)) := by
  have hm : (Generated.hostChunk039[0]).mask = 40695 := by decide +kernel
  have hv : ((Generated.hostChunk039[0]).induced.toList, (Generated.hostChunk039[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0468]

theorem fixed_values_0469 :
    (fixedDensityCounts (maskGraph 7 40698), fixedComplementCounts (maskGraph 7 40698)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0469_semantics :
    ((Generated.hostChunk039[1]).induced.toList, (Generated.hostChunk039[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[1]).mask)) := by
  have hm : (Generated.hostChunk039[1]).mask = 40698 := by decide +kernel
  have hv : ((Generated.hostChunk039[1]).induced.toList, (Generated.hostChunk039[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0469]

theorem fixed_values_0470 :
    (fixedDensityCounts (maskGraph 7 40699), fixedComplementCounts (maskGraph 7 40699)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0470_semantics :
    ((Generated.hostChunk039[2]).induced.toList, (Generated.hostChunk039[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[2]).mask)) := by
  have hm : (Generated.hostChunk039[2]).mask = 40699 := by decide +kernel
  have hv : ((Generated.hostChunk039[2]).induced.toList, (Generated.hostChunk039[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0470]

theorem fixed_values_0471 :
    (fixedDensityCounts (maskGraph 7 40702), fixedComplementCounts (maskGraph 7 40702)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 4, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0471_semantics :
    ((Generated.hostChunk039[3]).induced.toList, (Generated.hostChunk039[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[3]).mask)) := by
  have hm : (Generated.hostChunk039[3]).mask = 40702 := by decide +kernel
  have hv : ((Generated.hostChunk039[3]).induced.toList, (Generated.hostChunk039[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 4, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0471]

theorem fixed_values_0472 :
    (fixedDensityCounts (maskGraph 7 40703), fixedComplementCounts (maskGraph 7 40703)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 4, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0472_semantics :
    ((Generated.hostChunk039[4]).induced.toList, (Generated.hostChunk039[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[4]).mask)) := by
  have hm : (Generated.hostChunk039[4]).mask = 40703 := by decide +kernel
  have hv : ((Generated.hostChunk039[4]).induced.toList, (Generated.hostChunk039[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 4, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0472]

theorem fixed_values_0473 :
    (fixedDensityCounts (maskGraph 7 40958), fixedComplementCounts (maskGraph 7 40958)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0473_semantics :
    ((Generated.hostChunk039[5]).induced.toList, (Generated.hostChunk039[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[5]).mask)) := by
  have hm : (Generated.hostChunk039[5]).mask = 40958 := by decide +kernel
  have hv : ((Generated.hostChunk039[5]).induced.toList, (Generated.hostChunk039[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0473]

theorem fixed_values_0474 :
    (fixedDensityCounts (maskGraph 7 40959), fixedComplementCounts (maskGraph 7 40959)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0474_semantics :
    ((Generated.hostChunk039[6]).induced.toList, (Generated.hostChunk039[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[6]).mask)) := by
  have hm : (Generated.hostChunk039[6]).mask = 40959 := by decide +kernel
  have hv : ((Generated.hostChunk039[6]).induced.toList, (Generated.hostChunk039[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0474]

theorem fixed_values_0475 :
    (fixedDensityCounts (maskGraph 7 41950), fixedComplementCounts (maskGraph 7 41950)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0475_semantics :
    ((Generated.hostChunk039[7]).induced.toList, (Generated.hostChunk039[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[7]).mask)) := by
  have hm : (Generated.hostChunk039[7]).mask = 41950 := by decide +kernel
  have hv : ((Generated.hostChunk039[7]).induced.toList, (Generated.hostChunk039[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0475]

theorem fixed_values_0476 :
    (fixedDensityCounts (maskGraph 7 41951), fixedComplementCounts (maskGraph 7 41951)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0476_semantics :
    ((Generated.hostChunk039[8]).induced.toList, (Generated.hostChunk039[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[8]).mask)) := by
  have hm : (Generated.hostChunk039[8]).mask = 41951 := by decide +kernel
  have hv : ((Generated.hostChunk039[8]).induced.toList, (Generated.hostChunk039[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0476]

theorem fixed_values_0477 :
    (fixedDensityCounts (maskGraph 7 41952), fixedComplementCounts (maskGraph 7 41952)) =
      ([0, 0, 0, 0, 0, 0, 6, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0477_semantics :
    ((Generated.hostChunk039[9]).induced.toList, (Generated.hostChunk039[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[9]).mask)) := by
  have hm : (Generated.hostChunk039[9]).mask = 41952 := by decide +kernel
  have hv : ((Generated.hostChunk039[9]).induced.toList, (Generated.hostChunk039[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 6, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0477]

theorem fixed_values_0478 :
    (fixedDensityCounts (maskGraph 7 41953), fixedComplementCounts (maskGraph 7 41953)) =
      ([0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0478_semantics :
    ((Generated.hostChunk039[10]).induced.toList, (Generated.hostChunk039[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[10]).mask)) := by
  have hm : (Generated.hostChunk039[10]).mask = 41953 := by decide +kernel
  have hv : ((Generated.hostChunk039[10]).induced.toList, (Generated.hostChunk039[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 6, 0, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0478]

theorem fixed_values_0479 :
    (fixedDensityCounts (maskGraph 7 41954), fixedComplementCounts (maskGraph 7 41954)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 5, 4, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0479_semantics :
    ((Generated.hostChunk039[11]).induced.toList, (Generated.hostChunk039[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk039[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk039[11]).mask)) := by
  have hm : (Generated.hostChunk039[11]).mask = 41954 := by decide +kernel
  have hv : ((Generated.hostChunk039[11]).induced.toList, (Generated.hostChunk039[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 5, 4, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0479]

theorem fixed_chunk_039_semantics :
    ∀ h ∈ Generated.hostChunk039.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk039.toList = [Generated.hostChunk039[0], Generated.hostChunk039[1], Generated.hostChunk039[2], Generated.hostChunk039[3], Generated.hostChunk039[4], Generated.hostChunk039[5], Generated.hostChunk039[6], Generated.hostChunk039[7], Generated.hostChunk039[8], Generated.hostChunk039[9], Generated.hostChunk039[10], Generated.hostChunk039[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0468_semantics
  · exact fixed_host_0469_semantics
  · exact fixed_host_0470_semantics
  · exact fixed_host_0471_semantics
  · exact fixed_host_0472_semantics
  · exact fixed_host_0473_semantics
  · exact fixed_host_0474_semantics
  · exact fixed_host_0475_semantics
  · exact fixed_host_0476_semantics
  · exact fixed_host_0477_semantics
  · exact fixed_host_0478_semantics
  · exact fixed_host_0479_semantics

end InducedPentagons.Paper

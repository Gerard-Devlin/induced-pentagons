import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData056
import InducedPentagonsPaper.Generated.FixedRows048

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0672 :
    (fixedDensityCounts (maskGraph 7 48575), fixedComplementCounts (maskGraph 7 48575)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 4, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0672_semantics :
    ((Generated.hostChunk056[0]).induced.toList, (Generated.hostChunk056[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[0]).mask)) := by
  have hm : (Generated.hostChunk056[0]).mask = 48575 := by decide +kernel
  have hv : ((Generated.hostChunk056[0]).induced.toList, (Generated.hostChunk056[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 4, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0672]

theorem fixed_values_0673 :
    (fixedDensityCounts (maskGraph 7 48624), fixedComplementCounts (maskGraph 7 48624)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 1, 2, 6, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0673_semantics :
    ((Generated.hostChunk056[1]).induced.toList, (Generated.hostChunk056[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[1]).mask)) := by
  have hm : (Generated.hostChunk056[1]).mask = 48624 := by decide +kernel
  have hv : ((Generated.hostChunk056[1]).induced.toList, (Generated.hostChunk056[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 1, 2, 6, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0673]

theorem fixed_values_0674 :
    (fixedDensityCounts (maskGraph 7 48625), fixedComplementCounts (maskGraph 7 48625)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 1, 2, 0, 3, 3, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0674_semantics :
    ((Generated.hostChunk056[2]).induced.toList, (Generated.hostChunk056[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[2]).mask)) := by
  have hm : (Generated.hostChunk056[2]).mask = 48625 := by decide +kernel
  have hv : ((Generated.hostChunk056[2]).induced.toList, (Generated.hostChunk056[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 1, 2, 0, 3, 3, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0674]

theorem fixed_values_0675 :
    (fixedDensityCounts (maskGraph 7 48627), fixedComplementCounts (maskGraph 7 48627)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 5, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0675_semantics :
    ((Generated.hostChunk056[3]).induced.toList, (Generated.hostChunk056[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[3]).mask)) := by
  have hm : (Generated.hostChunk056[3]).mask = 48627 := by decide +kernel
  have hv : ((Generated.hostChunk056[3]).induced.toList, (Generated.hostChunk056[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 5, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0675]

theorem fixed_values_0676 :
    (fixedDensityCounts (maskGraph 7 48628), fixedComplementCounts (maskGraph 7 48628)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 4, 0, 3, 0, 1, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0676_semantics :
    ((Generated.hostChunk056[4]).induced.toList, (Generated.hostChunk056[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[4]).mask)) := by
  have hm : (Generated.hostChunk056[4]).mask = 48628 := by decide +kernel
  have hv : ((Generated.hostChunk056[4]).induced.toList, (Generated.hostChunk056[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 4, 0, 3, 0, 1, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0676]

theorem fixed_values_0677 :
    (fixedDensityCounts (maskGraph 7 48629), fixedComplementCounts (maskGraph 7 48629)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 1, 1, 2, 1, 0, 3, 2, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0677_semantics :
    ((Generated.hostChunk056[5]).induced.toList, (Generated.hostChunk056[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[5]).mask)) := by
  have hm : (Generated.hostChunk056[5]).mask = 48629 := by decide +kernel
  have hv : ((Generated.hostChunk056[5]).induced.toList, (Generated.hostChunk056[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 1, 1, 2, 1, 0, 3, 2, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0677]

theorem fixed_values_0678 :
    (fixedDensityCounts (maskGraph 7 48631), fixedComplementCounts (maskGraph 7 48631)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 5, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0678_semantics :
    ((Generated.hostChunk056[6]).induced.toList, (Generated.hostChunk056[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[6]).mask)) := by
  have hm : (Generated.hostChunk056[6]).mask = 48631 := by decide +kernel
  have hv : ((Generated.hostChunk056[6]).induced.toList, (Generated.hostChunk056[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 5, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0678]

theorem fixed_values_0679 :
    (fixedDensityCounts (maskGraph 7 48636), fixedComplementCounts (maskGraph 7 48636)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 4, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0679_semantics :
    ((Generated.hostChunk056[7]).induced.toList, (Generated.hostChunk056[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[7]).mask)) := by
  have hm : (Generated.hostChunk056[7]).mask = 48636 := by decide +kernel
  have hv : ((Generated.hostChunk056[7]).induced.toList, (Generated.hostChunk056[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 4, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0679]

theorem fixed_values_0680 :
    (fixedDensityCounts (maskGraph 7 48637), fixedComplementCounts (maskGraph 7 48637)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 3, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0680_semantics :
    ((Generated.hostChunk056[8]).induced.toList, (Generated.hostChunk056[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[8]).mask)) := by
  have hm : (Generated.hostChunk056[8]).mask = 48637 := by decide +kernel
  have hv : ((Generated.hostChunk056[8]).induced.toList, (Generated.hostChunk056[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 3, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0680]

theorem fixed_values_0681 :
    (fixedDensityCounts (maskGraph 7 48639), fixedComplementCounts (maskGraph 7 48639)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 6, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0681_semantics :
    ((Generated.hostChunk056[9]).induced.toList, (Generated.hostChunk056[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[9]).mask)) := by
  have hm : (Generated.hostChunk056[9]).mask = 48639 := by decide +kernel
  have hv : ((Generated.hostChunk056[9]).induced.toList, (Generated.hostChunk056[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 6, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0681]

theorem fixed_values_0682 :
    (fixedDensityCounts (maskGraph 7 48689), fixedComplementCounts (maskGraph 7 48689)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 7, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0682_semantics :
    ((Generated.hostChunk056[10]).induced.toList, (Generated.hostChunk056[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[10]).mask)) := by
  have hm : (Generated.hostChunk056[10]).mask = 48689 := by decide +kernel
  have hv : ((Generated.hostChunk056[10]).induced.toList, (Generated.hostChunk056[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 7, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0682]

theorem fixed_values_0683 :
    (fixedDensityCounts (maskGraph 7 48690), fixedComplementCounts (maskGraph 7 48690)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0683_semantics :
    ((Generated.hostChunk056[11]).induced.toList, (Generated.hostChunk056[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk056[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk056[11]).mask)) := by
  have hm : (Generated.hostChunk056[11]).mask = 48690 := by decide +kernel
  have hv : ((Generated.hostChunk056[11]).induced.toList, (Generated.hostChunk056[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0683]

theorem fixed_chunk_056_semantics :
    ∀ h ∈ Generated.hostChunk056.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk056.toList = [Generated.hostChunk056[0], Generated.hostChunk056[1], Generated.hostChunk056[2], Generated.hostChunk056[3], Generated.hostChunk056[4], Generated.hostChunk056[5], Generated.hostChunk056[6], Generated.hostChunk056[7], Generated.hostChunk056[8], Generated.hostChunk056[9], Generated.hostChunk056[10], Generated.hostChunk056[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0672_semantics
  · exact fixed_host_0673_semantics
  · exact fixed_host_0674_semantics
  · exact fixed_host_0675_semantics
  · exact fixed_host_0676_semantics
  · exact fixed_host_0677_semantics
  · exact fixed_host_0678_semantics
  · exact fixed_host_0679_semantics
  · exact fixed_host_0680_semantics
  · exact fixed_host_0681_semantics
  · exact fixed_host_0682_semantics
  · exact fixed_host_0683_semantics

end InducedPentagons.Paper

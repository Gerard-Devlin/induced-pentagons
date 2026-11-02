import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData066
import InducedPentagonsPaper.Generated.FixedRows058

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0792 :
    (fixedDensityCounts (maskGraph 7 111595), fixedComplementCounts (maskGraph 7 111595)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 4, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0792_semantics :
    ((Generated.hostChunk066[0]).induced.toList, (Generated.hostChunk066[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[0]).mask)) := by
  have hm : (Generated.hostChunk066[0]).mask = 111595 := by decide +kernel
  have hv : ((Generated.hostChunk066[0]).induced.toList, (Generated.hostChunk066[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 4, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0792]

theorem fixed_values_0793 :
    (fixedDensityCounts (maskGraph 7 111598), fixedComplementCounts (maskGraph 7 111598)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 2, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0793_semantics :
    ((Generated.hostChunk066[1]).induced.toList, (Generated.hostChunk066[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[1]).mask)) := by
  have hm : (Generated.hostChunk066[1]).mask = 111598 := by decide +kernel
  have hv : ((Generated.hostChunk066[1]).induced.toList, (Generated.hostChunk066[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 2, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0793]

theorem fixed_values_0794 :
    (fixedDensityCounts (maskGraph 7 111599), fixedComplementCounts (maskGraph 7 111599)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 3, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 2, 1, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0794_semantics :
    ((Generated.hostChunk066[2]).induced.toList, (Generated.hostChunk066[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[2]).mask)) := by
  have hm : (Generated.hostChunk066[2]).mask = 111599 := by decide +kernel
  have hv : ((Generated.hostChunk066[2]).induced.toList, (Generated.hostChunk066[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 3, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 2, 1, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0794]

theorem fixed_values_0795 :
    (fixedDensityCounts (maskGraph 7 111614), fixedComplementCounts (maskGraph 7 111614)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 2, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0795_semantics :
    ((Generated.hostChunk066[3]).induced.toList, (Generated.hostChunk066[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[3]).mask)) := by
  have hm : (Generated.hostChunk066[3]).mask = 111614 := by decide +kernel
  have hv : ((Generated.hostChunk066[3]).induced.toList, (Generated.hostChunk066[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 2, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0795]

theorem fixed_values_0796 :
    (fixedDensityCounts (maskGraph 7 111615), fixedComplementCounts (maskGraph 7 111615)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0796_semantics :
    ((Generated.hostChunk066[4]).induced.toList, (Generated.hostChunk066[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[4]).mask)) := by
  have hm : (Generated.hostChunk066[4]).mask = 111615 := by decide +kernel
  have hv : ((Generated.hostChunk066[4]).induced.toList, (Generated.hostChunk066[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0796]

theorem fixed_values_0797 :
    (fixedDensityCounts (maskGraph 7 111979), fixedComplementCounts (maskGraph 7 111979)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 4, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0797_semantics :
    ((Generated.hostChunk066[5]).induced.toList, (Generated.hostChunk066[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[5]).mask)) := by
  have hm : (Generated.hostChunk066[5]).mask = 111979 := by decide +kernel
  have hv : ((Generated.hostChunk066[5]).induced.toList, (Generated.hostChunk066[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 4, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0797]

theorem fixed_values_0798 :
    (fixedDensityCounts (maskGraph 7 111980), fixedComplementCounts (maskGraph 7 111980)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0798_semantics :
    ((Generated.hostChunk066[6]).induced.toList, (Generated.hostChunk066[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[6]).mask)) := by
  have hm : (Generated.hostChunk066[6]).mask = 111980 := by decide +kernel
  have hv : ((Generated.hostChunk066[6]).induced.toList, (Generated.hostChunk066[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0798]

theorem fixed_values_0799 :
    (fixedDensityCounts (maskGraph 7 111981), fixedComplementCounts (maskGraph 7 111981)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 5, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0799_semantics :
    ((Generated.hostChunk066[7]).induced.toList, (Generated.hostChunk066[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[7]).mask)) := by
  have hm : (Generated.hostChunk066[7]).mask = 111981 := by decide +kernel
  have hv : ((Generated.hostChunk066[7]).induced.toList, (Generated.hostChunk066[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 5, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0799]

theorem fixed_values_0800 :
    (fixedDensityCounts (maskGraph 7 111982), fixedComplementCounts (maskGraph 7 111982)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 5, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0800_semantics :
    ((Generated.hostChunk066[8]).induced.toList, (Generated.hostChunk066[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[8]).mask)) := by
  have hm : (Generated.hostChunk066[8]).mask = 111982 := by decide +kernel
  have hv : ((Generated.hostChunk066[8]).induced.toList, (Generated.hostChunk066[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 5, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0800]

theorem fixed_values_0801 :
    (fixedDensityCounts (maskGraph 7 111983), fixedComplementCounts (maskGraph 7 111983)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 1, 2, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 1, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0801_semantics :
    ((Generated.hostChunk066[9]).induced.toList, (Generated.hostChunk066[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[9]).mask)) := by
  have hm : (Generated.hostChunk066[9]).mask = 111983 := by decide +kernel
  have hv : ((Generated.hostChunk066[9]).induced.toList, (Generated.hostChunk066[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 1, 2, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 1, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0801]

theorem fixed_values_0802 :
    (fixedDensityCounts (maskGraph 7 111988), fixedComplementCounts (maskGraph 7 111988)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0802_semantics :
    ((Generated.hostChunk066[10]).induced.toList, (Generated.hostChunk066[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[10]).mask)) := by
  have hm : (Generated.hostChunk066[10]).mask = 111988 := by decide +kernel
  have hv : ((Generated.hostChunk066[10]).induced.toList, (Generated.hostChunk066[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0802]

theorem fixed_values_0803 :
    (fixedDensityCounts (maskGraph 7 111989), fixedComplementCounts (maskGraph 7 111989)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0803_semantics :
    ((Generated.hostChunk066[11]).induced.toList, (Generated.hostChunk066[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk066[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk066[11]).mask)) := by
  have hm : (Generated.hostChunk066[11]).mask = 111989 := by decide +kernel
  have hv : ((Generated.hostChunk066[11]).induced.toList, (Generated.hostChunk066[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0803]

theorem fixed_chunk_066_semantics :
    ∀ h ∈ Generated.hostChunk066.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk066.toList = [Generated.hostChunk066[0], Generated.hostChunk066[1], Generated.hostChunk066[2], Generated.hostChunk066[3], Generated.hostChunk066[4], Generated.hostChunk066[5], Generated.hostChunk066[6], Generated.hostChunk066[7], Generated.hostChunk066[8], Generated.hostChunk066[9], Generated.hostChunk066[10], Generated.hostChunk066[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0792_semantics
  · exact fixed_host_0793_semantics
  · exact fixed_host_0794_semantics
  · exact fixed_host_0795_semantics
  · exact fixed_host_0796_semantics
  · exact fixed_host_0797_semantics
  · exact fixed_host_0798_semantics
  · exact fixed_host_0799_semantics
  · exact fixed_host_0800_semantics
  · exact fixed_host_0801_semantics
  · exact fixed_host_0802_semantics
  · exact fixed_host_0803_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData068
import InducedPentagonsPaper.Generated.FixedRows060

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0816 :
    (fixedDensityCounts (maskGraph 7 112638), fixedComplementCounts (maskGraph 7 112638)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0816_semantics :
    ((Generated.hostChunk068[0]).induced.toList, (Generated.hostChunk068[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[0]).mask)) := by
  have hm : (Generated.hostChunk068[0]).mask = 112638 := by decide +kernel
  have hv : ((Generated.hostChunk068[0]).induced.toList, (Generated.hostChunk068[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0816]

theorem fixed_values_0817 :
    (fixedDensityCounts (maskGraph 7 112639), fixedComplementCounts (maskGraph 7 112639)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0817_semantics :
    ((Generated.hostChunk068[1]).induced.toList, (Generated.hostChunk068[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[1]).mask)) := by
  have hm : (Generated.hostChunk068[1]).mask = 112639 := by decide +kernel
  have hv : ((Generated.hostChunk068[1]).induced.toList, (Generated.hostChunk068[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0817]

theorem fixed_values_0818 :
    (fixedDensityCounts (maskGraph 7 113631), fixedComplementCounts (maskGraph 7 113631)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0818_semantics :
    ((Generated.hostChunk068[2]).induced.toList, (Generated.hostChunk068[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[2]).mask)) := by
  have hm : (Generated.hostChunk068[2]).mask = 113631 := by decide +kernel
  have hv : ((Generated.hostChunk068[2]).induced.toList, (Generated.hostChunk068[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0818]

theorem fixed_values_0819 :
    (fixedDensityCounts (maskGraph 7 113640), fixedComplementCounts (maskGraph 7 113640)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 3, 4, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0819_semantics :
    ((Generated.hostChunk068[3]).induced.toList, (Generated.hostChunk068[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[3]).mask)) := by
  have hm : (Generated.hostChunk068[3]).mask = 113640 := by decide +kernel
  have hv : ((Generated.hostChunk068[3]).induced.toList, (Generated.hostChunk068[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 3, 4, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0819]

theorem fixed_values_0820 :
    (fixedDensityCounts (maskGraph 7 113641), fixedComplementCounts (maskGraph 7 113641)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 2, 1, 4, 3, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 1, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0820_semantics :
    ((Generated.hostChunk068[4]).induced.toList, (Generated.hostChunk068[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[4]).mask)) := by
  have hm : (Generated.hostChunk068[4]).mask = 113641 := by decide +kernel
  have hv : ((Generated.hostChunk068[4]).induced.toList, (Generated.hostChunk068[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 2, 1, 4, 3, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 1, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0820]

theorem fixed_values_0821 :
    (fixedDensityCounts (maskGraph 7 113643), fixedComplementCounts (maskGraph 7 113643)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0, 2, 0, 2, 4, 1, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 1, 0, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0821_semantics :
    ((Generated.hostChunk068[5]).induced.toList, (Generated.hostChunk068[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[5]).mask)) := by
  have hm : (Generated.hostChunk068[5]).mask = 113643 := by decide +kernel
  have hv : ((Generated.hostChunk068[5]).induced.toList, (Generated.hostChunk068[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0, 2, 0, 2, 4, 1, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 1, 0, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0821]

theorem fixed_values_0822 :
    (fixedDensityCounts (maskGraph 7 113647), fixedComplementCounts (maskGraph 7 113647)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0822_semantics :
    ((Generated.hostChunk068[6]).induced.toList, (Generated.hostChunk068[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[6]).mask)) := by
  have hm : (Generated.hostChunk068[6]).mask = 113647 := by decide +kernel
  have hv : ((Generated.hostChunk068[6]).induced.toList, (Generated.hostChunk068[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0822]

theorem fixed_values_0823 :
    (fixedDensityCounts (maskGraph 7 113656), fixedComplementCounts (maskGraph 7 113656)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 2, 1, 6, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0823_semantics :
    ((Generated.hostChunk068[7]).induced.toList, (Generated.hostChunk068[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[7]).mask)) := by
  have hm : (Generated.hostChunk068[7]).mask = 113656 := by decide +kernel
  have hv : ((Generated.hostChunk068[7]).induced.toList, (Generated.hostChunk068[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 2, 1, 6, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0823]

theorem fixed_values_0824 :
    (fixedDensityCounts (maskGraph 7 113657), fixedComplementCounts (maskGraph 7 113657)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 1, 0, 0, 2, 0, 3, 4, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0824_semantics :
    ((Generated.hostChunk068[8]).induced.toList, (Generated.hostChunk068[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[8]).mask)) := by
  have hm : (Generated.hostChunk068[8]).mask = 113657 := by decide +kernel
  have hv : ((Generated.hostChunk068[8]).induced.toList, (Generated.hostChunk068[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 1, 0, 0, 2, 0, 3, 4, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0824]

theorem fixed_values_0825 :
    (fixedDensityCounts (maskGraph 7 113659), fixedComplementCounts (maskGraph 7 113659)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 2, 0, 0, 5, 2, 0, 0, 0, 0, 0, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 2, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0825_semantics :
    ((Generated.hostChunk068[9]).induced.toList, (Generated.hostChunk068[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[9]).mask)) := by
  have hm : (Generated.hostChunk068[9]).mask = 113659 := by decide +kernel
  have hv : ((Generated.hostChunk068[9]).induced.toList, (Generated.hostChunk068[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 2, 0, 0, 5, 2, 0, 0, 0, 0, 0, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 2, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0825]

theorem fixed_values_0826 :
    (fixedDensityCounts (maskGraph 7 113663), fixedComplementCounts (maskGraph 7 113663)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0826_semantics :
    ((Generated.hostChunk068[10]).induced.toList, (Generated.hostChunk068[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[10]).mask)) := by
  have hm : (Generated.hostChunk068[10]).mask = 113663 := by decide +kernel
  have hv : ((Generated.hostChunk068[10]).induced.toList, (Generated.hostChunk068[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0826]

theorem fixed_values_0827 :
    (fixedDensityCounts (maskGraph 7 113961), fixedComplementCounts (maskGraph 7 113961)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 6, 4, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0827_semantics :
    ((Generated.hostChunk068[11]).induced.toList, (Generated.hostChunk068[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk068[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk068[11]).mask)) := by
  have hm : (Generated.hostChunk068[11]).mask = 113961 := by decide +kernel
  have hv : ((Generated.hostChunk068[11]).induced.toList, (Generated.hostChunk068[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 6, 4, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0827]

theorem fixed_chunk_068_semantics :
    ∀ h ∈ Generated.hostChunk068.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk068.toList = [Generated.hostChunk068[0], Generated.hostChunk068[1], Generated.hostChunk068[2], Generated.hostChunk068[3], Generated.hostChunk068[4], Generated.hostChunk068[5], Generated.hostChunk068[6], Generated.hostChunk068[7], Generated.hostChunk068[8], Generated.hostChunk068[9], Generated.hostChunk068[10], Generated.hostChunk068[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0816_semantics
  · exact fixed_host_0817_semantics
  · exact fixed_host_0818_semantics
  · exact fixed_host_0819_semantics
  · exact fixed_host_0820_semantics
  · exact fixed_host_0821_semantics
  · exact fixed_host_0822_semantics
  · exact fixed_host_0823_semantics
  · exact fixed_host_0824_semantics
  · exact fixed_host_0825_semantics
  · exact fixed_host_0826_semantics
  · exact fixed_host_0827_semantics

end InducedPentagons.Paper

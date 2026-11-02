import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData054
import InducedPentagonsPaper.Generated.FixedRows046

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0648 :
    (fixedDensityCounts (maskGraph 7 48060), fixedComplementCounts (maskGraph 7 48060)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 1, 2, 1, 0, 0, 4, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0648_semantics :
    ((Generated.hostChunk054[0]).induced.toList, (Generated.hostChunk054[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[0]).mask)) := by
  have hm : (Generated.hostChunk054[0]).mask = 48060 := by decide +kernel
  have hv : ((Generated.hostChunk054[0]).induced.toList, (Generated.hostChunk054[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 1, 2, 1, 0, 0, 4, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0648]

theorem fixed_values_0649 :
    (fixedDensityCounts (maskGraph 7 48061), fixedComplementCounts (maskGraph 7 48061)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 3, 2, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0649_semantics :
    ((Generated.hostChunk054[1]).induced.toList, (Generated.hostChunk054[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[1]).mask)) := by
  have hm : (Generated.hostChunk054[1]).mask = 48061 := by decide +kernel
  have hv : ((Generated.hostChunk054[1]).induced.toList, (Generated.hostChunk054[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 3, 2, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0649]

theorem fixed_values_0650 :
    (fixedDensityCounts (maskGraph 7 48063), fixedComplementCounts (maskGraph 7 48063)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0650_semantics :
    ((Generated.hostChunk054[2]).induced.toList, (Generated.hostChunk054[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[2]).mask)) := by
  have hm : (Generated.hostChunk054[2]).mask = 48063 := by decide +kernel
  have hv : ((Generated.hostChunk054[2]).induced.toList, (Generated.hostChunk054[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0650]

theorem fixed_values_0651 :
    (fixedDensityCounts (maskGraph 7 48095), fixedComplementCounts (maskGraph 7 48095)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0651_semantics :
    ((Generated.hostChunk054[3]).induced.toList, (Generated.hostChunk054[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[3]).mask)) := by
  have hm : (Generated.hostChunk054[3]).mask = 48095 := by decide +kernel
  have hv : ((Generated.hostChunk054[3]).induced.toList, (Generated.hostChunk054[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0651]

theorem fixed_values_0652 :
    (fixedDensityCounts (maskGraph 7 48108), fixedComplementCounts (maskGraph 7 48108)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 1, 1, 2, 6, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0652_semantics :
    ((Generated.hostChunk054[4]).induced.toList, (Generated.hostChunk054[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[4]).mask)) := by
  have hm : (Generated.hostChunk054[4]).mask = 48108 := by decide +kernel
  have hv : ((Generated.hostChunk054[4]).induced.toList, (Generated.hostChunk054[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 1, 1, 2, 6, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0652]

theorem fixed_values_0653 :
    (fixedDensityCounts (maskGraph 7 48109), fixedComplementCounts (maskGraph 7 48109)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 0, 1, 4, 2, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0653_semantics :
    ((Generated.hostChunk054[5]).induced.toList, (Generated.hostChunk054[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[5]).mask)) := by
  have hm : (Generated.hostChunk054[5]).mask = 48109 := by decide +kernel
  have hv : ((Generated.hostChunk054[5]).induced.toList, (Generated.hostChunk054[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 0, 1, 4, 2, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0653]

theorem fixed_values_0654 :
    (fixedDensityCounts (maskGraph 7 48111), fixedComplementCounts (maskGraph 7 48111)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1, 6, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0654_semantics :
    ((Generated.hostChunk054[6]).induced.toList, (Generated.hostChunk054[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[6]).mask)) := by
  have hm : (Generated.hostChunk054[6]).mask = 48111 := by decide +kernel
  have hv : ((Generated.hostChunk054[6]).induced.toList, (Generated.hostChunk054[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1, 6, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0654]

theorem fixed_values_0655 :
    (fixedDensityCounts (maskGraph 7 48112), fixedComplementCounts (maskGraph 7 48112)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 2, 4, 3, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0655_semantics :
    ((Generated.hostChunk054[7]).induced.toList, (Generated.hostChunk054[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[7]).mask)) := by
  have hm : (Generated.hostChunk054[7]).mask = 48112 := by decide +kernel
  have hv : ((Generated.hostChunk054[7]).induced.toList, (Generated.hostChunk054[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 2, 4, 3, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0655]

theorem fixed_values_0656 :
    (fixedDensityCounts (maskGraph 7 48113), fixedComplementCounts (maskGraph 7 48113)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 4, 1, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0656_semantics :
    ((Generated.hostChunk054[8]).induced.toList, (Generated.hostChunk054[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[8]).mask)) := by
  have hm : (Generated.hostChunk054[8]).mask = 48113 := by decide +kernel
  have hv : ((Generated.hostChunk054[8]).induced.toList, (Generated.hostChunk054[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 4, 1, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0656]

theorem fixed_values_0657 :
    (fixedDensityCounts (maskGraph 7 48115), fixedComplementCounts (maskGraph 7 48115)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0657_semantics :
    ((Generated.hostChunk054[9]).induced.toList, (Generated.hostChunk054[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[9]).mask)) := by
  have hm : (Generated.hostChunk054[9]).mask = 48115 := by decide +kernel
  have hv : ((Generated.hostChunk054[9]).induced.toList, (Generated.hostChunk054[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0657]

theorem fixed_values_0658 :
    (fixedDensityCounts (maskGraph 7 48116), fixedComplementCounts (maskGraph 7 48116)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 2, 0, 2, 0, 0, 0, 1, 1, 4, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0658_semantics :
    ((Generated.hostChunk054[10]).induced.toList, (Generated.hostChunk054[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[10]).mask)) := by
  have hm : (Generated.hostChunk054[10]).mask = 48116 := by decide +kernel
  have hv : ((Generated.hostChunk054[10]).induced.toList, (Generated.hostChunk054[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 2, 0, 2, 0, 0, 0, 1, 1, 4, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0658]

theorem fixed_values_0659 :
    (fixedDensityCounts (maskGraph 7 48117), fixedComplementCounts (maskGraph 7 48117)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 1, 1, 1, 0, 0, 1, 0, 2, 3, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0659_semantics :
    ((Generated.hostChunk054[11]).induced.toList, (Generated.hostChunk054[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk054[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk054[11]).mask)) := by
  have hm : (Generated.hostChunk054[11]).mask = 48117 := by decide +kernel
  have hv : ((Generated.hostChunk054[11]).induced.toList, (Generated.hostChunk054[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 1, 1, 1, 0, 0, 1, 0, 2, 3, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0659]

theorem fixed_chunk_054_semantics :
    ∀ h ∈ Generated.hostChunk054.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk054.toList = [Generated.hostChunk054[0], Generated.hostChunk054[1], Generated.hostChunk054[2], Generated.hostChunk054[3], Generated.hostChunk054[4], Generated.hostChunk054[5], Generated.hostChunk054[6], Generated.hostChunk054[7], Generated.hostChunk054[8], Generated.hostChunk054[9], Generated.hostChunk054[10], Generated.hostChunk054[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0648_semantics
  · exact fixed_host_0649_semantics
  · exact fixed_host_0650_semantics
  · exact fixed_host_0651_semantics
  · exact fixed_host_0652_semantics
  · exact fixed_host_0653_semantics
  · exact fixed_host_0654_semantics
  · exact fixed_host_0655_semantics
  · exact fixed_host_0656_semantics
  · exact fixed_host_0657_semantics
  · exact fixed_host_0658_semantics
  · exact fixed_host_0659_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData012
import InducedPentagonsPaper.Generated.FixedRows004

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0144 :
    (fixedDensityCounts (maskGraph 7 2879), fixedComplementCounts (maskGraph 7 2879)) =
      ([0, 1, 2, 0, 2, 0, 2, 0, 0, 1, 0, 8, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0144_semantics :
    ((Generated.hostChunk012[0]).induced.toList, (Generated.hostChunk012[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[0]).mask)) := by
  have hm : (Generated.hostChunk012[0]).mask = 2879 := by decide +kernel
  have hv : ((Generated.hostChunk012[0]).induced.toList, (Generated.hostChunk012[0]).complement.toList) =
      ([0, 1, 2, 0, 2, 0, 2, 0, 0, 1, 0, 8, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0144]

theorem fixed_values_0145 :
    (fixedDensityCounts (maskGraph 7 2906), fixedComplementCounts (maskGraph 7 2906)) =
      ([0, 1, 4, 3, 0, 0, 0, 4, 0, 0, 2, 0, 4, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0145_semantics :
    ((Generated.hostChunk012[1]).induced.toList, (Generated.hostChunk012[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[1]).mask)) := by
  have hm : (Generated.hostChunk012[1]).mask = 2906 := by decide +kernel
  have hv : ((Generated.hostChunk012[1]).induced.toList, (Generated.hostChunk012[1]).complement.toList) =
      ([0, 1, 4, 3, 0, 0, 0, 4, 0, 0, 2, 0, 4, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0145]

theorem fixed_values_0146 :
    (fixedDensityCounts (maskGraph 7 2907), fixedComplementCounts (maskGraph 7 2907)) =
      ([0, 1, 2, 2, 0, 2, 0, 4, 1, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0146_semantics :
    ((Generated.hostChunk012[2]).induced.toList, (Generated.hostChunk012[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[2]).mask)) := by
  have hm : (Generated.hostChunk012[2]).mask = 2907 := by decide +kernel
  have hv : ((Generated.hostChunk012[2]).induced.toList, (Generated.hostChunk012[2]).complement.toList) =
      ([0, 1, 2, 2, 0, 2, 0, 4, 1, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0146]

theorem fixed_values_0147 :
    (fixedDensityCounts (maskGraph 7 2908), fixedComplementCounts (maskGraph 7 2908)) =
      ([0, 1, 2, 2, 0, 0, 0, 9, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0147_semantics :
    ((Generated.hostChunk012[3]).induced.toList, (Generated.hostChunk012[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[3]).mask)) := by
  have hm : (Generated.hostChunk012[3]).mask = 2908 := by decide +kernel
  have hv : ((Generated.hostChunk012[3]).induced.toList, (Generated.hostChunk012[3]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 0, 9, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0147]

theorem fixed_values_0148 :
    (fixedDensityCounts (maskGraph 7 2909), fixedComplementCounts (maskGraph 7 2909)) =
      ([0, 1, 2, 2, 0, 0, 0, 4, 4, 0, 2, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0148_semantics :
    ((Generated.hostChunk012[4]).induced.toList, (Generated.hostChunk012[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[4]).mask)) := by
  have hm : (Generated.hostChunk012[4]).mask = 2909 := by decide +kernel
  have hv : ((Generated.hostChunk012[4]).induced.toList, (Generated.hostChunk012[4]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 0, 4, 4, 0, 2, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0148]

theorem fixed_values_0149 :
    (fixedDensityCounts (maskGraph 7 2910), fixedComplementCounts (maskGraph 7 2910)) =
      ([0, 1, 1, 3, 0, 0, 0, 4, 3, 0, 1, 1, 3, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0149_semantics :
    ((Generated.hostChunk012[5]).induced.toList, (Generated.hostChunk012[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[5]).mask)) := by
  have hm : (Generated.hostChunk012[5]).mask = 2910 := by decide +kernel
  have hv : ((Generated.hostChunk012[5]).induced.toList, (Generated.hostChunk012[5]).complement.toList) =
      ([0, 1, 1, 3, 0, 0, 0, 4, 3, 0, 1, 1, 3, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0149]

theorem fixed_values_0150 :
    (fixedDensityCounts (maskGraph 7 2911), fixedComplementCounts (maskGraph 7 2911)) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 4, 0, 1, 1, 0, 4, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0150_semantics :
    ((Generated.hostChunk012[6]).induced.toList, (Generated.hostChunk012[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[6]).mask)) := by
  have hm : (Generated.hostChunk012[6]).mask = 2911 := by decide +kernel
  have hv : ((Generated.hostChunk012[6]).induced.toList, (Generated.hostChunk012[6]).complement.toList) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 4, 0, 1, 1, 0, 4, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0150]

theorem fixed_values_0151 :
    (fixedDensityCounts (maskGraph 7 2922), fixedComplementCounts (maskGraph 7 2922)) =
      ([0, 1, 2, 2, 0, 0, 1, 6, 0, 0, 4, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0151_semantics :
    ((Generated.hostChunk012[7]).induced.toList, (Generated.hostChunk012[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[7]).mask)) := by
  have hm : (Generated.hostChunk012[7]).mask = 2922 := by decide +kernel
  have hv : ((Generated.hostChunk012[7]).induced.toList, (Generated.hostChunk012[7]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 1, 6, 0, 0, 4, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0151]

theorem fixed_values_0152 :
    (fixedDensityCounts (maskGraph 7 2923), fixedComplementCounts (maskGraph 7 2923)) =
      ([0, 1, 2, 2, 0, 0, 0, 5, 2, 0, 2, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0152_semantics :
    ((Generated.hostChunk012[8]).induced.toList, (Generated.hostChunk012[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[8]).mask)) := by
  have hm : (Generated.hostChunk012[8]).mask = 2923 := by decide +kernel
  have hv : ((Generated.hostChunk012[8]).induced.toList, (Generated.hostChunk012[8]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 0, 5, 2, 0, 2, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0152]

theorem fixed_values_0153 :
    (fixedDensityCounts (maskGraph 7 2924), fixedComplementCounts (maskGraph 7 2924)) =
      ([0, 1, 2, 2, 0, 0, 0, 4, 0, 2, 4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0153_semantics :
    ((Generated.hostChunk012[9]).induced.toList, (Generated.hostChunk012[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[9]).mask)) := by
  have hm : (Generated.hostChunk012[9]).mask = 2924 := by decide +kernel
  have hv : ((Generated.hostChunk012[9]).induced.toList, (Generated.hostChunk012[9]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 0, 4, 0, 2, 4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0153]

theorem fixed_values_0154 :
    (fixedDensityCounts (maskGraph 7 2925), fixedComplementCounts (maskGraph 7 2925)) =
      ([0, 1, 2, 2, 0, 0, 0, 4, 0, 0, 4, 2, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0154_semantics :
    ((Generated.hostChunk012[10]).induced.toList, (Generated.hostChunk012[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[10]).mask)) := by
  have hm : (Generated.hostChunk012[10]).mask = 2925 := by decide +kernel
  have hv : ((Generated.hostChunk012[10]).induced.toList, (Generated.hostChunk012[10]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 0, 4, 0, 0, 4, 2, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0154]

theorem fixed_values_0155 :
    (fixedDensityCounts (maskGraph 7 2926), fixedComplementCounts (maskGraph 7 2926)) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 2, 1, 2, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0155_semantics :
    ((Generated.hostChunk012[11]).induced.toList, (Generated.hostChunk012[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk012[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk012[11]).mask)) := by
  have hm : (Generated.hostChunk012[11]).mask = 2926 := by decide +kernel
  have hv : ((Generated.hostChunk012[11]).induced.toList, (Generated.hostChunk012[11]).complement.toList) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 2, 1, 2, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0155]

theorem fixed_chunk_012_semantics :
    ∀ h ∈ Generated.hostChunk012.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk012.toList = [Generated.hostChunk012[0], Generated.hostChunk012[1], Generated.hostChunk012[2], Generated.hostChunk012[3], Generated.hostChunk012[4], Generated.hostChunk012[5], Generated.hostChunk012[6], Generated.hostChunk012[7], Generated.hostChunk012[8], Generated.hostChunk012[9], Generated.hostChunk012[10], Generated.hostChunk012[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0144_semantics
  · exact fixed_host_0145_semantics
  · exact fixed_host_0146_semantics
  · exact fixed_host_0147_semantics
  · exact fixed_host_0148_semantics
  · exact fixed_host_0149_semantics
  · exact fixed_host_0150_semantics
  · exact fixed_host_0151_semantics
  · exact fixed_host_0152_semantics
  · exact fixed_host_0153_semantics
  · exact fixed_host_0154_semantics
  · exact fixed_host_0155_semantics

end InducedPentagons.Paper

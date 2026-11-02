import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData069
import InducedPentagonsPaper.Generated.FixedRows061

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0828 :
    (fixedDensityCounts (maskGraph 7 113963), fixedComplementCounts (maskGraph 7 113963)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0, 0, 2, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0828_semantics :
    ((Generated.hostChunk069[0]).induced.toList, (Generated.hostChunk069[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[0]).mask)) := by
  have hm : (Generated.hostChunk069[0]).mask = 113963 := by decide +kernel
  have hv : ((Generated.hostChunk069[0]).induced.toList, (Generated.hostChunk069[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0, 0, 2, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0828]

theorem fixed_values_0829 :
    (fixedDensityCounts (maskGraph 7 113967), fixedComplementCounts (maskGraph 7 113967)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 3, 5, 1, 1, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0829_semantics :
    ((Generated.hostChunk069[1]).induced.toList, (Generated.hostChunk069[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[1]).mask)) := by
  have hm : (Generated.hostChunk069[1]).mask = 113967 := by decide +kernel
  have hv : ((Generated.hostChunk069[1]).induced.toList, (Generated.hostChunk069[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 3, 5, 1, 1, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0829]

theorem fixed_values_0830 :
    (fixedDensityCounts (maskGraph 7 113969), fixedComplementCounts (maskGraph 7 113969)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 3, 8, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0830_semantics :
    ((Generated.hostChunk069[2]).induced.toList, (Generated.hostChunk069[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[2]).mask)) := by
  have hm : (Generated.hostChunk069[2]).mask = 113969 := by decide +kernel
  have hv : ((Generated.hostChunk069[2]).induced.toList, (Generated.hostChunk069[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 3, 8, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0830]

theorem fixed_values_0831 :
    (fixedDensityCounts (maskGraph 7 113970), fixedComplementCounts (maskGraph 7 113970)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 2, 0, 0, 0, 0, 0, 1, 4, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0831_semantics :
    ((Generated.hostChunk069[3]).induced.toList, (Generated.hostChunk069[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[3]).mask)) := by
  have hm : (Generated.hostChunk069[3]).mask = 113970 := by decide +kernel
  have hv : ((Generated.hostChunk069[3]).induced.toList, (Generated.hostChunk069[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 2, 0, 0, 0, 0, 0, 1, 4, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0831]

theorem fixed_values_0832 :
    (fixedDensityCounts (maskGraph 7 113971), fixedComplementCounts (maskGraph 7 113971)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 0, 0, 0, 1, 5, 3, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 2, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0832_semantics :
    ((Generated.hostChunk069[4]).induced.toList, (Generated.hostChunk069[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[4]).mask)) := by
  have hm : (Generated.hostChunk069[4]).mask = 113971 := by decide +kernel
  have hv : ((Generated.hostChunk069[4]).induced.toList, (Generated.hostChunk069[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 0, 0, 0, 1, 5, 3, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 2, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0832]

theorem fixed_values_0833 :
    (fixedDensityCounts (maskGraph 7 113974), fixedComplementCounts (maskGraph 7 113974)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 0, 0, 1, 1, 6, 3, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0833_semantics :
    ((Generated.hostChunk069[5]).induced.toList, (Generated.hostChunk069[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[5]).mask)) := by
  have hm : (Generated.hostChunk069[5]).mask = 113974 := by decide +kernel
  have hv : ((Generated.hostChunk069[5]).induced.toList, (Generated.hostChunk069[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 0, 0, 1, 1, 6, 3, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0833]

theorem fixed_values_0834 :
    (fixedDensityCounts (maskGraph 7 113975), fixedComplementCounts (maskGraph 7 113975)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 0, 4, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 2, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0834_semantics :
    ((Generated.hostChunk069[6]).induced.toList, (Generated.hostChunk069[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[6]).mask)) := by
  have hm : (Generated.hostChunk069[6]).mask = 113975 := by decide +kernel
  have hv : ((Generated.hostChunk069[6]).induced.toList, (Generated.hostChunk069[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 0, 4, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 2, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0834]

theorem fixed_values_0835 :
    (fixedDensityCounts (maskGraph 7 113977), fixedComplementCounts (maskGraph 7 113977)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 2, 6, 3, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 4, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0835_semantics :
    ((Generated.hostChunk069[7]).induced.toList, (Generated.hostChunk069[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[7]).mask)) := by
  have hm : (Generated.hostChunk069[7]).mask = 113977 := by decide +kernel
  have hv : ((Generated.hostChunk069[7]).induced.toList, (Generated.hostChunk069[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 2, 6, 3, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 4, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0835]

theorem fixed_values_0836 :
    (fixedDensityCounts (maskGraph 7 113978), fixedComplementCounts (maskGraph 7 113978)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 2, 0, 0, 0, 1, 2, 4, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0836_semantics :
    ((Generated.hostChunk069[8]).induced.toList, (Generated.hostChunk069[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[8]).mask)) := by
  have hm : (Generated.hostChunk069[8]).mask = 113978 := by decide +kernel
  have hv : ((Generated.hostChunk069[8]).induced.toList, (Generated.hostChunk069[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 2, 0, 0, 0, 1, 2, 4, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0836]

theorem fixed_values_0837 :
    (fixedDensityCounts (maskGraph 7 113979), fixedComplementCounts (maskGraph 7 113979)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 1, 3, 5, 0, 1, 0, 1, 3, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0837_semantics :
    ((Generated.hostChunk069[9]).induced.toList, (Generated.hostChunk069[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[9]).mask)) := by
  have hm : (Generated.hostChunk069[9]).mask = 113979 := by decide +kernel
  have hv : ((Generated.hostChunk069[9]).induced.toList, (Generated.hostChunk069[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 1, 3, 5, 0, 1, 0, 1, 3, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0837]

theorem fixed_values_0838 :
    (fixedDensityCounts (maskGraph 7 113982), fixedComplementCounts (maskGraph 7 113982)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 2, 0, 0, 1, 1, 4, 3, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 3, 1, 1, 0, 0, 2, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0838_semantics :
    ((Generated.hostChunk069[10]).induced.toList, (Generated.hostChunk069[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[10]).mask)) := by
  have hm : (Generated.hostChunk069[10]).mask = 113982 := by decide +kernel
  have hv : ((Generated.hostChunk069[10]).induced.toList, (Generated.hostChunk069[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 2, 0, 0, 1, 1, 4, 3, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 3, 1, 1, 0, 0, 2, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0838]

theorem fixed_values_0839 :
    (fixedDensityCounts (maskGraph 7 113983), fixedComplementCounts (maskGraph 7 113983)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 1, 1, 1, 3, 3, 0, 0, 4, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 2, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0839_semantics :
    ((Generated.hostChunk069[11]).induced.toList, (Generated.hostChunk069[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk069[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk069[11]).mask)) := by
  have hm : (Generated.hostChunk069[11]).mask = 113983 := by decide +kernel
  have hv : ((Generated.hostChunk069[11]).induced.toList, (Generated.hostChunk069[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 1, 1, 1, 3, 3, 0, 0, 4, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 2, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0839]

theorem fixed_chunk_069_semantics :
    ∀ h ∈ Generated.hostChunk069.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk069.toList = [Generated.hostChunk069[0], Generated.hostChunk069[1], Generated.hostChunk069[2], Generated.hostChunk069[3], Generated.hostChunk069[4], Generated.hostChunk069[5], Generated.hostChunk069[6], Generated.hostChunk069[7], Generated.hostChunk069[8], Generated.hostChunk069[9], Generated.hostChunk069[10], Generated.hostChunk069[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0828_semantics
  · exact fixed_host_0829_semantics
  · exact fixed_host_0830_semantics
  · exact fixed_host_0831_semantics
  · exact fixed_host_0832_semantics
  · exact fixed_host_0833_semantics
  · exact fixed_host_0834_semantics
  · exact fixed_host_0835_semantics
  · exact fixed_host_0836_semantics
  · exact fixed_host_0837_semantics
  · exact fixed_host_0838_semantics
  · exact fixed_host_0839_semantics

end InducedPentagons.Paper

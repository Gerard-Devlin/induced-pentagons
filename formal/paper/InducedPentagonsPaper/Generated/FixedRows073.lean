import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData073
import InducedPentagonsPaper.Generated.FixedRows065

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0876 :
    (fixedDensityCounts (maskGraph 7 114686), fixedComplementCounts (maskGraph 7 114686)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0876_semantics :
    ((Generated.hostChunk073[0]).induced.toList, (Generated.hostChunk073[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[0]).mask)) := by
  have hm : (Generated.hostChunk073[0]).mask = 114686 := by decide +kernel
  have hv : ((Generated.hostChunk073[0]).induced.toList, (Generated.hostChunk073[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0876]

theorem fixed_values_0877 :
    (fixedDensityCounts (maskGraph 7 114687), fixedComplementCounts (maskGraph 7 114687)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 5, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0877_semantics :
    ((Generated.hostChunk073[1]).induced.toList, (Generated.hostChunk073[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[1]).mask)) := by
  have hm : (Generated.hostChunk073[1]).mask = 114687 := by decide +kernel
  have hv : ((Generated.hostChunk073[1]).induced.toList, (Generated.hostChunk073[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 5, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0877]

theorem fixed_values_0878 :
    (fixedDensityCounts (maskGraph 7 120383), fixedComplementCounts (maskGraph 7 120383)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0878_semantics :
    ((Generated.hostChunk073[2]).induced.toList, (Generated.hostChunk073[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[2]).mask)) := by
  have hm : (Generated.hostChunk073[2]).mask = 120383 := by decide +kernel
  have hv : ((Generated.hostChunk073[2]).induced.toList, (Generated.hostChunk073[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0878]

theorem fixed_values_0879 :
    (fixedDensityCounts (maskGraph 7 120443), fixedComplementCounts (maskGraph 7 120443)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0, 1, 0, 4, 4, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0879_semantics :
    ((Generated.hostChunk073[3]).induced.toList, (Generated.hostChunk073[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[3]).mask)) := by
  have hm : (Generated.hostChunk073[3]).mask = 120443 := by decide +kernel
  have hv : ((Generated.hostChunk073[3]).induced.toList, (Generated.hostChunk073[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0, 1, 0, 4, 4, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0879]

theorem fixed_values_0880 :
    (fixedDensityCounts (maskGraph 7 120444), fixedComplementCounts (maskGraph 7 120444)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 0, 0, 7, 2, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0880_semantics :
    ((Generated.hostChunk073[4]).induced.toList, (Generated.hostChunk073[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[4]).mask)) := by
  have hm : (Generated.hostChunk073[4]).mask = 120444 := by decide +kernel
  have hv : ((Generated.hostChunk073[4]).induced.toList, (Generated.hostChunk073[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 0, 0, 7, 2, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0880]

theorem fixed_values_0881 :
    (fixedDensityCounts (maskGraph 7 120445), fixedComplementCounts (maskGraph 7 120445)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0, 0, 0, 3, 3, 0, 1, 1, 3, 3, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0881_semantics :
    ((Generated.hostChunk073[5]).induced.toList, (Generated.hostChunk073[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[5]).mask)) := by
  have hm : (Generated.hostChunk073[5]).mask = 120445 := by decide +kernel
  have hv : ((Generated.hostChunk073[5]).induced.toList, (Generated.hostChunk073[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0, 0, 0, 3, 3, 0, 1, 1, 3, 3, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0881]

theorem fixed_values_0882 :
    (fixedDensityCounts (maskGraph 7 120447), fixedComplementCounts (maskGraph 7 120447)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 0, 0, 0, 0, 2, 0, 1, 2, 1, 0, 7, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 4, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0882_semantics :
    ((Generated.hostChunk073[6]).induced.toList, (Generated.hostChunk073[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[6]).mask)) := by
  have hm : (Generated.hostChunk073[6]).mask = 120447 := by decide +kernel
  have hv : ((Generated.hostChunk073[6]).induced.toList, (Generated.hostChunk073[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 0, 0, 0, 0, 2, 0, 1, 2, 1, 0, 7, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 4, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0882]

theorem fixed_values_0883 :
    (fixedDensityCounts (maskGraph 7 120568), fixedComplementCounts (maskGraph 7 120568)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 6, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0883_semantics :
    ((Generated.hostChunk073[7]).induced.toList, (Generated.hostChunk073[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[7]).mask)) := by
  have hm : (Generated.hostChunk073[7]).mask = 120568 := by decide +kernel
  have hv : ((Generated.hostChunk073[7]).induced.toList, (Generated.hostChunk073[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 6, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0883]

theorem fixed_values_0884 :
    (fixedDensityCounts (maskGraph 7 120569), fixedComplementCounts (maskGraph 7 120569)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 3, 1, 0, 0, 0, 0, 0, 0, 1, 0, 4, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0884_semantics :
    ((Generated.hostChunk073[8]).induced.toList, (Generated.hostChunk073[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[8]).mask)) := by
  have hm : (Generated.hostChunk073[8]).mask = 120569 := by decide +kernel
  have hv : ((Generated.hostChunk073[8]).induced.toList, (Generated.hostChunk073[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 3, 1, 0, 0, 0, 0, 0, 0, 1, 0, 4, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0884]

theorem fixed_values_0885 :
    (fixedDensityCounts (maskGraph 7 120570), fixedComplementCounts (maskGraph 7 120570)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 1, 2, 0, 1, 1, 8, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 5, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0885_semantics :
    ((Generated.hostChunk073[9]).induced.toList, (Generated.hostChunk073[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[9]).mask)) := by
  have hm : (Generated.hostChunk073[9]).mask = 120570 := by decide +kernel
  have hv : ((Generated.hostChunk073[9]).induced.toList, (Generated.hostChunk073[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 1, 2, 0, 1, 1, 8, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 5, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0885]

theorem fixed_values_0886 :
    (fixedDensityCounts (maskGraph 7 120571), fixedComplementCounts (maskGraph 7 120571)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 4, 3, 2, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 1, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0886_semantics :
    ((Generated.hostChunk073[10]).induced.toList, (Generated.hostChunk073[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[10]).mask)) := by
  have hm : (Generated.hostChunk073[10]).mask = 120571 := by decide +kernel
  have hv : ((Generated.hostChunk073[10]).induced.toList, (Generated.hostChunk073[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 4, 3, 2, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 1, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0886]

theorem fixed_values_0887 :
    (fixedDensityCounts (maskGraph 7 120574), fixedComplementCounts (maskGraph 7 120574)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 4, 5, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 4, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0887_semantics :
    ((Generated.hostChunk073[11]).induced.toList, (Generated.hostChunk073[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk073[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk073[11]).mask)) := by
  have hm : (Generated.hostChunk073[11]).mask = 120574 := by decide +kernel
  have hv : ((Generated.hostChunk073[11]).induced.toList, (Generated.hostChunk073[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 4, 5, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 4, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0887]

theorem fixed_chunk_073_semantics :
    ∀ h ∈ Generated.hostChunk073.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk073.toList = [Generated.hostChunk073[0], Generated.hostChunk073[1], Generated.hostChunk073[2], Generated.hostChunk073[3], Generated.hostChunk073[4], Generated.hostChunk073[5], Generated.hostChunk073[6], Generated.hostChunk073[7], Generated.hostChunk073[8], Generated.hostChunk073[9], Generated.hostChunk073[10], Generated.hostChunk073[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0876_semantics
  · exact fixed_host_0877_semantics
  · exact fixed_host_0878_semantics
  · exact fixed_host_0879_semantics
  · exact fixed_host_0880_semantics
  · exact fixed_host_0881_semantics
  · exact fixed_host_0882_semantics
  · exact fixed_host_0883_semantics
  · exact fixed_host_0884_semantics
  · exact fixed_host_0885_semantics
  · exact fixed_host_0886_semantics
  · exact fixed_host_0887_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData011
import InducedPentagonsPaper.Generated.FixedRows003

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0132 :
    (fixedDensityCounts (maskGraph 7 2847), fixedComplementCounts (maskGraph 7 2847)) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 7, 1, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0132_semantics :
    ((Generated.hostChunk011[0]).induced.toList, (Generated.hostChunk011[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[0]).mask)) := by
  have hm : (Generated.hostChunk011[0]).mask = 2847 := by decide +kernel
  have hv : ((Generated.hostChunk011[0]).induced.toList, (Generated.hostChunk011[0]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 7, 1, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0132]

theorem fixed_values_0133 :
    (fixedDensityCounts (maskGraph 7 2856), fixedComplementCounts (maskGraph 7 2856)) =
      ([0, 1, 4, 0, 0, 0, 8, 4, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0133_semantics :
    ((Generated.hostChunk011[1]).induced.toList, (Generated.hostChunk011[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[1]).mask)) := by
  have hm : (Generated.hostChunk011[1]).mask = 2856 := by decide +kernel
  have hv : ((Generated.hostChunk011[1]).induced.toList, (Generated.hostChunk011[1]).complement.toList) =
      ([0, 1, 4, 0, 0, 0, 8, 4, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0133]

theorem fixed_values_0134 :
    (fixedDensityCounts (maskGraph 7 2857), fixedComplementCounts (maskGraph 7 2857)) =
      ([0, 1, 4, 0, 0, 0, 4, 2, 4, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0134_semantics :
    ((Generated.hostChunk011[2]).induced.toList, (Generated.hostChunk011[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[2]).mask)) := by
  have hm : (Generated.hostChunk011[2]).mask = 2857 := by decide +kernel
  have hv : ((Generated.hostChunk011[2]).induced.toList, (Generated.hostChunk011[2]).complement.toList) =
      ([0, 1, 4, 0, 0, 0, 4, 2, 4, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0134]

theorem fixed_values_0135 :
    (fixedDensityCounts (maskGraph 7 2858), fixedComplementCounts (maskGraph 7 2858)) =
      ([0, 1, 3, 1, 0, 0, 3, 5, 0, 3, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0135_semantics :
    ((Generated.hostChunk011[3]).induced.toList, (Generated.hostChunk011[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[3]).mask)) := by
  have hm : (Generated.hostChunk011[3]).mask = 2858 := by decide +kernel
  have hv : ((Generated.hostChunk011[3]).induced.toList, (Generated.hostChunk011[3]).complement.toList) =
      ([0, 1, 3, 1, 0, 0, 3, 5, 0, 3, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0135]

theorem fixed_values_0136 :
    (fixedDensityCounts (maskGraph 7 2859), fixedComplementCounts (maskGraph 7 2859)) =
      ([0, 1, 3, 1, 0, 0, 2, 3, 2, 1, 3, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0136_semantics :
    ((Generated.hostChunk011[4]).induced.toList, (Generated.hostChunk011[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[4]).mask)) := by
  have hm : (Generated.hostChunk011[4]).mask = 2859 := by decide +kernel
  have hv : ((Generated.hostChunk011[4]).induced.toList, (Generated.hostChunk011[4]).complement.toList) =
      ([0, 1, 3, 1, 0, 0, 2, 3, 2, 1, 3, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0136]

theorem fixed_values_0137 :
    (fixedDensityCounts (maskGraph 7 2862), fixedComplementCounts (maskGraph 7 2862)) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 3, 3, 2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0137_semantics :
    ((Generated.hostChunk011[5]).induced.toList, (Generated.hostChunk011[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[5]).mask)) := by
  have hm : (Generated.hostChunk011[5]).mask = 2862 := by decide +kernel
  have hv : ((Generated.hostChunk011[5]).induced.toList, (Generated.hostChunk011[5]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 3, 3, 2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0137]

theorem fixed_values_0138 :
    (fixedDensityCounts (maskGraph 7 2863), fixedComplementCounts (maskGraph 7 2863)) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 2, 1, 2, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0138_semantics :
    ((Generated.hostChunk011[6]).induced.toList, (Generated.hostChunk011[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[6]).mask)) := by
  have hm : (Generated.hostChunk011[6]).mask = 2863 := by decide +kernel
  have hv : ((Generated.hostChunk011[6]).induced.toList, (Generated.hostChunk011[6]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 2, 1, 2, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0138]

theorem fixed_values_0139 :
    (fixedDensityCounts (maskGraph 7 2872), fixedComplementCounts (maskGraph 7 2872)) =
      ([0, 1, 2, 2, 0, 0, 3, 4, 0, 6, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0139_semantics :
    ((Generated.hostChunk011[7]).induced.toList, (Generated.hostChunk011[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[7]).mask)) := by
  have hm : (Generated.hostChunk011[7]).mask = 2872 := by decide +kernel
  have hv : ((Generated.hostChunk011[7]).induced.toList, (Generated.hostChunk011[7]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 3, 4, 0, 6, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0139]

theorem fixed_values_0140 :
    (fixedDensityCounts (maskGraph 7 2873), fixedComplementCounts (maskGraph 7 2873)) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 4, 5, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0140_semantics :
    ((Generated.hostChunk011[8]).induced.toList, (Generated.hostChunk011[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[8]).mask)) := by
  have hm : (Generated.hostChunk011[8]).mask = 2873 := by decide +kernel
  have hv : ((Generated.hostChunk011[8]).induced.toList, (Generated.hostChunk011[8]).complement.toList) =
      ([0, 1, 2, 2, 0, 0, 2, 0, 4, 5, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0140]

theorem fixed_values_0141 :
    (fixedDensityCounts (maskGraph 7 2874), fixedComplementCounts (maskGraph 7 2874)) =
      ([0, 1, 2, 1, 1, 0, 2, 3, 0, 1, 5, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0141_semantics :
    ((Generated.hostChunk011[9]).induced.toList, (Generated.hostChunk011[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[9]).mask)) := by
  have hm : (Generated.hostChunk011[9]).mask = 2874 := by decide +kernel
  have hv : ((Generated.hostChunk011[9]).induced.toList, (Generated.hostChunk011[9]).complement.toList) =
      ([0, 1, 2, 1, 1, 0, 2, 3, 0, 1, 5, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0141]

theorem fixed_values_0142 :
    (fixedDensityCounts (maskGraph 7 2875), fixedComplementCounts (maskGraph 7 2875)) =
      ([0, 1, 2, 1, 1, 0, 2, 0, 2, 1, 4, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0142_semantics :
    ((Generated.hostChunk011[10]).induced.toList, (Generated.hostChunk011[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[10]).mask)) := by
  have hm : (Generated.hostChunk011[10]).mask = 2875 := by decide +kernel
  have hv : ((Generated.hostChunk011[10]).induced.toList, (Generated.hostChunk011[10]).complement.toList) =
      ([0, 1, 2, 1, 1, 0, 2, 0, 2, 1, 4, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0142]

theorem fixed_values_0143 :
    (fixedDensityCounts (maskGraph 7 2878), fixedComplementCounts (maskGraph 7 2878)) =
      ([0, 1, 2, 0, 2, 0, 2, 0, 1, 1, 4, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0143_semantics :
    ((Generated.hostChunk011[11]).induced.toList, (Generated.hostChunk011[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk011[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk011[11]).mask)) := by
  have hm : (Generated.hostChunk011[11]).mask = 2878 := by decide +kernel
  have hv : ((Generated.hostChunk011[11]).induced.toList, (Generated.hostChunk011[11]).complement.toList) =
      ([0, 1, 2, 0, 2, 0, 2, 0, 1, 1, 4, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0143]

theorem fixed_chunk_011_semantics :
    ∀ h ∈ Generated.hostChunk011.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk011.toList = [Generated.hostChunk011[0], Generated.hostChunk011[1], Generated.hostChunk011[2], Generated.hostChunk011[3], Generated.hostChunk011[4], Generated.hostChunk011[5], Generated.hostChunk011[6], Generated.hostChunk011[7], Generated.hostChunk011[8], Generated.hostChunk011[9], Generated.hostChunk011[10], Generated.hostChunk011[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0132_semantics
  · exact fixed_host_0133_semantics
  · exact fixed_host_0134_semantics
  · exact fixed_host_0135_semantics
  · exact fixed_host_0136_semantics
  · exact fixed_host_0137_semantics
  · exact fixed_host_0138_semantics
  · exact fixed_host_0139_semantics
  · exact fixed_host_0140_semantics
  · exact fixed_host_0141_semantics
  · exact fixed_host_0142_semantics
  · exact fixed_host_0143_semantics

end InducedPentagons.Paper

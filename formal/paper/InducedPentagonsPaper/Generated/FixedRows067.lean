import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData067
import InducedPentagonsPaper.Generated.FixedRows059

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0804 :
    (fixedDensityCounts (maskGraph 7 111990), fixedComplementCounts (maskGraph 7 111990)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 2, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0804_semantics :
    ((Generated.hostChunk067[0]).induced.toList, (Generated.hostChunk067[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[0]).mask)) := by
  have hm : (Generated.hostChunk067[0]).mask = 111990 := by decide +kernel
  have hv : ((Generated.hostChunk067[0]).induced.toList, (Generated.hostChunk067[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 2, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0804]

theorem fixed_values_0805 :
    (fixedDensityCounts (maskGraph 7 111991), fixedComplementCounts (maskGraph 7 111991)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 5, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0805_semantics :
    ((Generated.hostChunk067[1]).induced.toList, (Generated.hostChunk067[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[1]).mask)) := by
  have hm : (Generated.hostChunk067[1]).mask = 111991 := by decide +kernel
  have hv : ((Generated.hostChunk067[1]).induced.toList, (Generated.hostChunk067[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 5, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0805]

theorem fixed_values_0806 :
    (fixedDensityCounts (maskGraph 7 111998), fixedComplementCounts (maskGraph 7 111998)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 2, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 1, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0806_semantics :
    ((Generated.hostChunk067[2]).induced.toList, (Generated.hostChunk067[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[2]).mask)) := by
  have hm : (Generated.hostChunk067[2]).mask = 111998 := by decide +kernel
  have hv : ((Generated.hostChunk067[2]).induced.toList, (Generated.hostChunk067[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 2, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 1, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0806]

theorem fixed_values_0807 :
    (fixedDensityCounts (maskGraph 7 111999), fixedComplementCounts (maskGraph 7 111999)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 4, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 1, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0807_semantics :
    ((Generated.hostChunk067[3]).induced.toList, (Generated.hostChunk067[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[3]).mask)) := by
  have hm : (Generated.hostChunk067[3]).mask = 111999 := by decide +kernel
  have hv : ((Generated.hostChunk067[3]).induced.toList, (Generated.hostChunk067[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 4, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 1, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0807]

theorem fixed_values_0808 :
    (fixedDensityCounts (maskGraph 7 112110), fixedComplementCounts (maskGraph 7 112110)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 4, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0808_semantics :
    ((Generated.hostChunk067[4]).induced.toList, (Generated.hostChunk067[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[4]).mask)) := by
  have hm : (Generated.hostChunk067[4]).mask = 112110 := by decide +kernel
  have hv : ((Generated.hostChunk067[4]).induced.toList, (Generated.hostChunk067[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 4, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0808]

theorem fixed_values_0809 :
    (fixedDensityCounts (maskGraph 7 112111), fixedComplementCounts (maskGraph 7 112111)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 4, 2, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 3, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0809_semantics :
    ((Generated.hostChunk067[5]).induced.toList, (Generated.hostChunk067[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[5]).mask)) := by
  have hm : (Generated.hostChunk067[5]).mask = 112111 := by decide +kernel
  have hv : ((Generated.hostChunk067[5]).induced.toList, (Generated.hostChunk067[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 4, 2, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 3, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0809]

theorem fixed_values_0810 :
    (fixedDensityCounts (maskGraph 7 112118), fixedComplementCounts (maskGraph 7 112118)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 4, 2, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0810_semantics :
    ((Generated.hostChunk067[6]).induced.toList, (Generated.hostChunk067[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[6]).mask)) := by
  have hm : (Generated.hostChunk067[6]).mask = 112118 := by decide +kernel
  have hv : ((Generated.hostChunk067[6]).induced.toList, (Generated.hostChunk067[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 4, 2, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0810]

theorem fixed_values_0811 :
    (fixedDensityCounts (maskGraph 7 112119), fixedComplementCounts (maskGraph 7 112119)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0811_semantics :
    ((Generated.hostChunk067[7]).induced.toList, (Generated.hostChunk067[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[7]).mask)) := by
  have hm : (Generated.hostChunk067[7]).mask = 112119 := by decide +kernel
  have hv : ((Generated.hostChunk067[7]).induced.toList, (Generated.hostChunk067[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0811]

theorem fixed_values_0812 :
    (fixedDensityCounts (maskGraph 7 112122), fixedComplementCounts (maskGraph 7 112122)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0812_semantics :
    ((Generated.hostChunk067[8]).induced.toList, (Generated.hostChunk067[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[8]).mask)) := by
  have hm : (Generated.hostChunk067[8]).mask = 112122 := by decide +kernel
  have hv : ((Generated.hostChunk067[8]).induced.toList, (Generated.hostChunk067[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0812]

theorem fixed_values_0813 :
    (fixedDensityCounts (maskGraph 7 112123), fixedComplementCounts (maskGraph 7 112123)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0813_semantics :
    ((Generated.hostChunk067[9]).induced.toList, (Generated.hostChunk067[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[9]).mask)) := by
  have hm : (Generated.hostChunk067[9]).mask = 112123 := by decide +kernel
  have hv : ((Generated.hostChunk067[9]).induced.toList, (Generated.hostChunk067[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0813]

theorem fixed_values_0814 :
    (fixedDensityCounts (maskGraph 7 112126), fixedComplementCounts (maskGraph 7 112126)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0814_semantics :
    ((Generated.hostChunk067[10]).induced.toList, (Generated.hostChunk067[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[10]).mask)) := by
  have hm : (Generated.hostChunk067[10]).mask = 112126 := by decide +kernel
  have hv : ((Generated.hostChunk067[10]).induced.toList, (Generated.hostChunk067[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0814]

theorem fixed_values_0815 :
    (fixedDensityCounts (maskGraph 7 112127), fixedComplementCounts (maskGraph 7 112127)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 4, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0815_semantics :
    ((Generated.hostChunk067[11]).induced.toList, (Generated.hostChunk067[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk067[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk067[11]).mask)) := by
  have hm : (Generated.hostChunk067[11]).mask = 112127 := by decide +kernel
  have hv : ((Generated.hostChunk067[11]).induced.toList, (Generated.hostChunk067[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 4, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0815]

theorem fixed_chunk_067_semantics :
    ∀ h ∈ Generated.hostChunk067.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk067.toList = [Generated.hostChunk067[0], Generated.hostChunk067[1], Generated.hostChunk067[2], Generated.hostChunk067[3], Generated.hostChunk067[4], Generated.hostChunk067[5], Generated.hostChunk067[6], Generated.hostChunk067[7], Generated.hostChunk067[8], Generated.hostChunk067[9], Generated.hostChunk067[10], Generated.hostChunk067[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0804_semantics
  · exact fixed_host_0805_semantics
  · exact fixed_host_0806_semantics
  · exact fixed_host_0807_semantics
  · exact fixed_host_0808_semantics
  · exact fixed_host_0809_semantics
  · exact fixed_host_0810_semantics
  · exact fixed_host_0811_semantics
  · exact fixed_host_0812_semantics
  · exact fixed_host_0813_semantics
  · exact fixed_host_0814_semantics
  · exact fixed_host_0815_semantics

end InducedPentagons.Paper

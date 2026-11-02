import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData053
import InducedPentagonsPaper.Generated.FixedRows045

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0636 :
    (fixedDensityCounts (maskGraph 7 45055), fixedComplementCounts (maskGraph 7 45055)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 5, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0636_semantics :
    ((Generated.hostChunk053[0]).induced.toList, (Generated.hostChunk053[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[0]).mask)) := by
  have hm : (Generated.hostChunk053[0]).mask = 45055 := by decide +kernel
  have hv : ((Generated.hostChunk053[0]).induced.toList, (Generated.hostChunk053[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 5, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0636]

theorem fixed_values_0637 :
    (fixedDensityCounts (maskGraph 7 48029), fixedComplementCounts (maskGraph 7 48029)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0637_semantics :
    ((Generated.hostChunk053[1]).induced.toList, (Generated.hostChunk053[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[1]).mask)) := by
  have hm : (Generated.hostChunk053[1]).mask = 48029 := by decide +kernel
  have hv : ((Generated.hostChunk053[1]).induced.toList, (Generated.hostChunk053[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0637]

theorem fixed_values_0638 :
    (fixedDensityCounts (maskGraph 7 48031), fixedComplementCounts (maskGraph 7 48031)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 8, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 6, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0638_semantics :
    ((Generated.hostChunk053[2]).induced.toList, (Generated.hostChunk053[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[2]).mask)) := by
  have hm : (Generated.hostChunk053[2]).mask = 48031 := by decide +kernel
  have hv : ((Generated.hostChunk053[2]).induced.toList, (Generated.hostChunk053[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 8, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 6, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0638]

theorem fixed_values_0639 :
    (fixedDensityCounts (maskGraph 7 48044), fixedComplementCounts (maskGraph 7 48044)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 2, 1, 4, 0, 2, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0639_semantics :
    ((Generated.hostChunk053[3]).induced.toList, (Generated.hostChunk053[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[3]).mask)) := by
  have hm : (Generated.hostChunk053[3]).mask = 48044 := by decide +kernel
  have hv : ((Generated.hostChunk053[3]).induced.toList, (Generated.hostChunk053[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 2, 1, 4, 0, 2, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0639]

theorem fixed_values_0640 :
    (fixedDensityCounts (maskGraph 7 48045), fixedComplementCounts (maskGraph 7 48045)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1, 3, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0640_semantics :
    ((Generated.hostChunk053[4]).induced.toList, (Generated.hostChunk053[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[4]).mask)) := by
  have hm : (Generated.hostChunk053[4]).mask = 48045 := by decide +kernel
  have hv : ((Generated.hostChunk053[4]).induced.toList, (Generated.hostChunk053[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1, 3, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0640]

theorem fixed_values_0641 :
    (fixedDensityCounts (maskGraph 7 48047), fixedComplementCounts (maskGraph 7 48047)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1, 0, 4, 1, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0641_semantics :
    ((Generated.hostChunk053[5]).induced.toList, (Generated.hostChunk053[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[5]).mask)) := by
  have hm : (Generated.hostChunk053[5]).mask = 48047 := by decide +kernel
  have hv : ((Generated.hostChunk053[5]).induced.toList, (Generated.hostChunk053[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1, 0, 4, 1, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0641]

theorem fixed_values_0642 :
    (fixedDensityCounts (maskGraph 7 48048), fixedComplementCounts (maskGraph 7 48048)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 2, 2, 4, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0642_semantics :
    ((Generated.hostChunk053[6]).induced.toList, (Generated.hostChunk053[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[6]).mask)) := by
  have hm : (Generated.hostChunk053[6]).mask = 48048 := by decide +kernel
  have hv : ((Generated.hostChunk053[6]).induced.toList, (Generated.hostChunk053[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 2, 2, 4, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0642]

theorem fixed_values_0643 :
    (fixedDensityCounts (maskGraph 7 48049), fixedComplementCounts (maskGraph 7 48049)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 4, 3, 0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0643_semantics :
    ((Generated.hostChunk053[7]).induced.toList, (Generated.hostChunk053[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[7]).mask)) := by
  have hm : (Generated.hostChunk053[7]).mask = 48049 := by decide +kernel
  have hv : ((Generated.hostChunk053[7]).induced.toList, (Generated.hostChunk053[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 4, 3, 0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0643]

theorem fixed_values_0644 :
    (fixedDensityCounts (maskGraph 7 48051), fixedComplementCounts (maskGraph 7 48051)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 0, 4, 2, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0644_semantics :
    ((Generated.hostChunk053[8]).induced.toList, (Generated.hostChunk053[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[8]).mask)) := by
  have hm : (Generated.hostChunk053[8]).mask = 48051 := by decide +kernel
  have hv : ((Generated.hostChunk053[8]).induced.toList, (Generated.hostChunk053[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 0, 4, 2, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0644]

theorem fixed_values_0645 :
    (fixedDensityCounts (maskGraph 7 48052), fixedComplementCounts (maskGraph 7 48052)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 2, 1, 2, 0, 3, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0645_semantics :
    ((Generated.hostChunk053[9]).induced.toList, (Generated.hostChunk053[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[9]).mask)) := by
  have hm : (Generated.hostChunk053[9]).mask = 48052 := by decide +kernel
  have hv : ((Generated.hostChunk053[9]).induced.toList, (Generated.hostChunk053[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 2, 1, 2, 0, 3, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0645]

theorem fixed_values_0646 :
    (fixedDensityCounts (maskGraph 7 48053), fixedComplementCounts (maskGraph 7 48053)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 1, 2, 3, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0646_semantics :
    ((Generated.hostChunk053[10]).induced.toList, (Generated.hostChunk053[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[10]).mask)) := by
  have hm : (Generated.hostChunk053[10]).mask = 48053 := by decide +kernel
  have hv : ((Generated.hostChunk053[10]).induced.toList, (Generated.hostChunk053[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 1, 2, 3, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 2, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0646]

theorem fixed_values_0647 :
    (fixedDensityCounts (maskGraph 7 48055), fixedComplementCounts (maskGraph 7 48055)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 2, 1, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0647_semantics :
    ((Generated.hostChunk053[11]).induced.toList, (Generated.hostChunk053[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk053[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk053[11]).mask)) := by
  have hm : (Generated.hostChunk053[11]).mask = 48055 := by decide +kernel
  have hv : ((Generated.hostChunk053[11]).induced.toList, (Generated.hostChunk053[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 2, 1, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0647]

theorem fixed_chunk_053_semantics :
    ∀ h ∈ Generated.hostChunk053.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk053.toList = [Generated.hostChunk053[0], Generated.hostChunk053[1], Generated.hostChunk053[2], Generated.hostChunk053[3], Generated.hostChunk053[4], Generated.hostChunk053[5], Generated.hostChunk053[6], Generated.hostChunk053[7], Generated.hostChunk053[8], Generated.hostChunk053[9], Generated.hostChunk053[10], Generated.hostChunk053[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0636_semantics
  · exact fixed_host_0637_semantics
  · exact fixed_host_0638_semantics
  · exact fixed_host_0639_semantics
  · exact fixed_host_0640_semantics
  · exact fixed_host_0641_semantics
  · exact fixed_host_0642_semantics
  · exact fixed_host_0643_semantics
  · exact fixed_host_0644_semantics
  · exact fixed_host_0645_semantics
  · exact fixed_host_0646_semantics
  · exact fixed_host_0647_semantics

end InducedPentagons.Paper

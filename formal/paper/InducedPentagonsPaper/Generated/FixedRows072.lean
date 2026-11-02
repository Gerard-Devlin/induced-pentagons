import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData072
import InducedPentagonsPaper.Generated.FixedRows064

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0864 :
    (fixedDensityCounts (maskGraph 7 114175), fixedComplementCounts (maskGraph 7 114175)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 6, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 3, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0864_semantics :
    ((Generated.hostChunk072[0]).induced.toList, (Generated.hostChunk072[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[0]).mask)) := by
  have hm : (Generated.hostChunk072[0]).mask = 114175 := by decide +kernel
  have hv : ((Generated.hostChunk072[0]).induced.toList, (Generated.hostChunk072[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 6, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 3, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0864]

theorem fixed_values_0865 :
    (fixedDensityCounts (maskGraph 7 114489), fixedComplementCounts (maskGraph 7 114489)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 1, 0, 1, 4, 4, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 4, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0865_semantics :
    ((Generated.hostChunk072[1]).induced.toList, (Generated.hostChunk072[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[1]).mask)) := by
  have hm : (Generated.hostChunk072[1]).mask = 114489 := by decide +kernel
  have hv : ((Generated.hostChunk072[1]).induced.toList, (Generated.hostChunk072[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 1, 0, 1, 4, 4, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 4, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0865]

theorem fixed_values_0866 :
    (fixedDensityCounts (maskGraph 7 114490), fixedComplementCounts (maskGraph 7 114490)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 5, 3, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0866_semantics :
    ((Generated.hostChunk072[2]).induced.toList, (Generated.hostChunk072[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[2]).mask)) := by
  have hm : (Generated.hostChunk072[2]).mask = 114490 := by decide +kernel
  have hv : ((Generated.hostChunk072[2]).induced.toList, (Generated.hostChunk072[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 5, 3, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0866]

theorem fixed_values_0867 :
    (fixedDensityCounts (maskGraph 7 114491), fixedComplementCounts (maskGraph 7 114491)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 0, 0, 3, 4, 0, 0, 0, 0, 4, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 4, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0867_semantics :
    ((Generated.hostChunk072[3]).induced.toList, (Generated.hostChunk072[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[3]).mask)) := by
  have hm : (Generated.hostChunk072[3]).mask = 114491 := by decide +kernel
  have hv : ((Generated.hostChunk072[3]).induced.toList, (Generated.hostChunk072[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 0, 0, 3, 4, 0, 0, 0, 0, 4, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 4, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0867]

theorem fixed_values_0868 :
    (fixedDensityCounts (maskGraph 7 114494), fixedComplementCounts (maskGraph 7 114494)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 0, 3, 0, 4, 0, 0, 4, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 4, 0, 1, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0868_semantics :
    ((Generated.hostChunk072[4]).induced.toList, (Generated.hostChunk072[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[4]).mask)) := by
  have hm : (Generated.hostChunk072[4]).mask = 114494 := by decide +kernel
  have hv : ((Generated.hostChunk072[4]).induced.toList, (Generated.hostChunk072[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 0, 3, 0, 4, 0, 0, 4, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 4, 0, 1, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0868]

theorem fixed_values_0869 :
    (fixedDensityCounts (maskGraph 7 114495), fixedComplementCounts (maskGraph 7 114495)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 2, 1, 0, 0, 4, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 4, 1, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0869_semantics :
    ((Generated.hostChunk072[5]).induced.toList, (Generated.hostChunk072[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[5]).mask)) := by
  have hm : (Generated.hostChunk072[5]).mask = 114495 := by decide +kernel
  have hv : ((Generated.hostChunk072[5]).induced.toList, (Generated.hostChunk072[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 2, 1, 0, 0, 4, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 4, 1, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0869]

theorem fixed_values_0870 :
    (fixedDensityCounts (maskGraph 7 114554), fixedComplementCounts (maskGraph 7 114554)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 2, 2, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0870_semantics :
    ((Generated.hostChunk072[6]).induced.toList, (Generated.hostChunk072[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[6]).mask)) := by
  have hm : (Generated.hostChunk072[6]).mask = 114554 := by decide +kernel
  have hv : ((Generated.hostChunk072[6]).induced.toList, (Generated.hostChunk072[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 2, 2, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0870]

theorem fixed_values_0871 :
    (fixedDensityCounts (maskGraph 7 114555), fixedComplementCounts (maskGraph 7 114555)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 1, 4, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0871_semantics :
    ((Generated.hostChunk072[7]).induced.toList, (Generated.hostChunk072[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[7]).mask)) := by
  have hm : (Generated.hostChunk072[7]).mask = 114555 := by decide +kernel
  have hv : ((Generated.hostChunk072[7]).induced.toList, (Generated.hostChunk072[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 1, 4, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0871]

theorem fixed_values_0872 :
    (fixedDensityCounts (maskGraph 7 114556), fixedComplementCounts (maskGraph 7 114556)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 0, 0, 4, 0, 0, 1, 4, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0872_semantics :
    ((Generated.hostChunk072[8]).induced.toList, (Generated.hostChunk072[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[8]).mask)) := by
  have hm : (Generated.hostChunk072[8]).mask = 114556 := by decide +kernel
  have hv : ((Generated.hostChunk072[8]).induced.toList, (Generated.hostChunk072[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 0, 0, 4, 0, 0, 1, 4, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0872]

theorem fixed_values_0873 :
    (fixedDensityCounts (maskGraph 7 114557), fixedComplementCounts (maskGraph 7 114557)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 4, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0873_semantics :
    ((Generated.hostChunk072[9]).induced.toList, (Generated.hostChunk072[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[9]).mask)) := by
  have hm : (Generated.hostChunk072[9]).mask = 114557 := by decide +kernel
  have hv : ((Generated.hostChunk072[9]).induced.toList, (Generated.hostChunk072[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 4, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0873]

theorem fixed_values_0874 :
    (fixedDensityCounts (maskGraph 7 114558), fixedComplementCounts (maskGraph 7 114558)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 1, 0, 0, 0, 0, 2, 2, 0, 0, 3, 0, 3, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2, 0, 1, 1, 0]) := by
  decide +kernel

theorem fixed_host_0874_semantics :
    ((Generated.hostChunk072[10]).induced.toList, (Generated.hostChunk072[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[10]).mask)) := by
  have hm : (Generated.hostChunk072[10]).mask = 114558 := by decide +kernel
  have hv : ((Generated.hostChunk072[10]).induced.toList, (Generated.hostChunk072[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 1, 0, 0, 0, 0, 2, 2, 0, 0, 3, 0, 3, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2, 0, 1, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0874]

theorem fixed_values_0875 :
    (fixedDensityCounts (maskGraph 7 114559), fixedComplementCounts (maskGraph 7 114559)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 3, 0, 2, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 1, 1, 0]) := by
  decide +kernel

theorem fixed_host_0875_semantics :
    ((Generated.hostChunk072[11]).induced.toList, (Generated.hostChunk072[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk072[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk072[11]).mask)) := by
  have hm : (Generated.hostChunk072[11]).mask = 114559 := by decide +kernel
  have hv : ((Generated.hostChunk072[11]).induced.toList, (Generated.hostChunk072[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 3, 0, 2, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 1, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0875]

theorem fixed_chunk_072_semantics :
    ∀ h ∈ Generated.hostChunk072.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk072.toList = [Generated.hostChunk072[0], Generated.hostChunk072[1], Generated.hostChunk072[2], Generated.hostChunk072[3], Generated.hostChunk072[4], Generated.hostChunk072[5], Generated.hostChunk072[6], Generated.hostChunk072[7], Generated.hostChunk072[8], Generated.hostChunk072[9], Generated.hostChunk072[10], Generated.hostChunk072[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0864_semantics
  · exact fixed_host_0865_semantics
  · exact fixed_host_0866_semantics
  · exact fixed_host_0867_semantics
  · exact fixed_host_0868_semantics
  · exact fixed_host_0869_semantics
  · exact fixed_host_0870_semantics
  · exact fixed_host_0871_semantics
  · exact fixed_host_0872_semantics
  · exact fixed_host_0873_semantics
  · exact fixed_host_0874_semantics
  · exact fixed_host_0875_semantics

end InducedPentagons.Paper

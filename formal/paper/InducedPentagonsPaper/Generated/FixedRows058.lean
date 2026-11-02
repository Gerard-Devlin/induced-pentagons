import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData058
import InducedPentagonsPaper.Generated.FixedRows050

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0696 :
    (fixedDensityCounts (maskGraph 7 48757), fixedComplementCounts (maskGraph 7 48757)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 5, 1, 0, 1, 0, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0696_semantics :
    ((Generated.hostChunk058[0]).induced.toList, (Generated.hostChunk058[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[0]).mask)) := by
  have hm : (Generated.hostChunk058[0]).mask = 48757 := by decide +kernel
  have hv : ((Generated.hostChunk058[0]).induced.toList, (Generated.hostChunk058[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 5, 1, 0, 1, 0, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0696]

theorem fixed_values_0697 :
    (fixedDensityCounts (maskGraph 7 48758), fixedComplementCounts (maskGraph 7 48758)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 2, 3, 2, 3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0697_semantics :
    ((Generated.hostChunk058[1]).induced.toList, (Generated.hostChunk058[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[1]).mask)) := by
  have hm : (Generated.hostChunk058[1]).mask = 48758 := by decide +kernel
  have hv : ((Generated.hostChunk058[1]).induced.toList, (Generated.hostChunk058[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 2, 3, 2, 3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0697]

theorem fixed_values_0698 :
    (fixedDensityCounts (maskGraph 7 48759), fixedComplementCounts (maskGraph 7 48759)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 3, 2, 1, 1, 0, 0, 3, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0698_semantics :
    ((Generated.hostChunk058[2]).induced.toList, (Generated.hostChunk058[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[2]).mask)) := by
  have hm : (Generated.hostChunk058[2]).mask = 48759 := by decide +kernel
  have hv : ((Generated.hostChunk058[2]).induced.toList, (Generated.hostChunk058[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 3, 2, 1, 1, 0, 0, 3, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0698]

theorem fixed_values_0699 :
    (fixedDensityCounts (maskGraph 7 48764), fixedComplementCounts (maskGraph 7 48764)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 3, 2, 0, 1, 2, 3, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0699_semantics :
    ((Generated.hostChunk058[3]).induced.toList, (Generated.hostChunk058[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[3]).mask)) := by
  have hm : (Generated.hostChunk058[3]).mask = 48764 := by decide +kernel
  have hv : ((Generated.hostChunk058[3]).induced.toList, (Generated.hostChunk058[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 3, 2, 0, 1, 2, 3, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0699]

theorem fixed_values_0700 :
    (fixedDensityCounts (maskGraph 7 48765), fixedComplementCounts (maskGraph 7 48765)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 0, 3, 0, 2, 1, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0700_semantics :
    ((Generated.hostChunk058[4]).induced.toList, (Generated.hostChunk058[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[4]).mask)) := by
  have hm : (Generated.hostChunk058[4]).mask = 48765 := by decide +kernel
  have hv : ((Generated.hostChunk058[4]).induced.toList, (Generated.hostChunk058[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 0, 3, 0, 2, 1, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0700]

theorem fixed_values_0701 :
    (fixedDensityCounts (maskGraph 7 48766), fixedComplementCounts (maskGraph 7 48766)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 3, 0, 2, 1, 0, 2, 2, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0701_semantics :
    ((Generated.hostChunk058[5]).induced.toList, (Generated.hostChunk058[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[5]).mask)) := by
  have hm : (Generated.hostChunk058[5]).mask = 48766 := by decide +kernel
  have hv : ((Generated.hostChunk058[5]).induced.toList, (Generated.hostChunk058[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 3, 0, 2, 1, 0, 2, 2, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0701]

theorem fixed_values_0702 :
    (fixedDensityCounts (maskGraph 7 48767), fixedComplementCounts (maskGraph 7 48767)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0, 2, 0, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0702_semantics :
    ((Generated.hostChunk058[6]).induced.toList, (Generated.hostChunk058[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[6]).mask)) := by
  have hm : (Generated.hostChunk058[6]).mask = 48767 := by decide +kernel
  have hv : ((Generated.hostChunk058[6]).induced.toList, (Generated.hostChunk058[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0, 2, 0, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0702]

theorem fixed_values_0703 :
    (fixedDensityCounts (maskGraph 7 48820), fixedComplementCounts (maskGraph 7 48820)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 1, 1, 0, 2, 0, 6, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0703_semantics :
    ((Generated.hostChunk058[7]).induced.toList, (Generated.hostChunk058[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[7]).mask)) := by
  have hm : (Generated.hostChunk058[7]).mask = 48820 := by decide +kernel
  have hv : ((Generated.hostChunk058[7]).induced.toList, (Generated.hostChunk058[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 1, 1, 0, 2, 0, 6, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0703]

theorem fixed_values_0704 :
    (fixedDensityCounts (maskGraph 7 48821), fixedComplementCounts (maskGraph 7 48821)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 2, 0, 0, 1, 0, 1, 3, 4, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0704_semantics :
    ((Generated.hostChunk058[8]).induced.toList, (Generated.hostChunk058[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[8]).mask)) := by
  have hm : (Generated.hostChunk058[8]).mask = 48821 := by decide +kernel
  have hv : ((Generated.hostChunk058[8]).induced.toList, (Generated.hostChunk058[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 2, 0, 0, 1, 0, 1, 3, 4, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0704]

theorem fixed_values_0705 :
    (fixedDensityCounts (maskGraph 7 48822), fixedComplementCounts (maskGraph 7 48822)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 3, 2, 1, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0705_semantics :
    ((Generated.hostChunk058[9]).induced.toList, (Generated.hostChunk058[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[9]).mask)) := by
  have hm : (Generated.hostChunk058[9]).mask = 48822 := by decide +kernel
  have hv : ((Generated.hostChunk058[9]).induced.toList, (Generated.hostChunk058[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 3, 2, 1, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0705]

theorem fixed_values_0706 :
    (fixedDensityCounts (maskGraph 7 48823), fixedComplementCounts (maskGraph 7 48823)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 2, 4, 0, 0, 0, 1, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0706_semantics :
    ((Generated.hostChunk058[10]).induced.toList, (Generated.hostChunk058[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[10]).mask)) := by
  have hm : (Generated.hostChunk058[10]).mask = 48823 := by decide +kernel
  have hv : ((Generated.hostChunk058[10]).induced.toList, (Generated.hostChunk058[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 2, 4, 0, 0, 0, 1, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0706]

theorem fixed_values_0707 :
    (fixedDensityCounts (maskGraph 7 48824), fixedComplementCounts (maskGraph 7 48824)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 4, 1, 7, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0707_semantics :
    ((Generated.hostChunk058[11]).induced.toList, (Generated.hostChunk058[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk058[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk058[11]).mask)) := by
  have hm : (Generated.hostChunk058[11]).mask = 48824 := by decide +kernel
  have hv : ((Generated.hostChunk058[11]).induced.toList, (Generated.hostChunk058[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 4, 1, 7, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0707]

theorem fixed_chunk_058_semantics :
    ∀ h ∈ Generated.hostChunk058.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk058.toList = [Generated.hostChunk058[0], Generated.hostChunk058[1], Generated.hostChunk058[2], Generated.hostChunk058[3], Generated.hostChunk058[4], Generated.hostChunk058[5], Generated.hostChunk058[6], Generated.hostChunk058[7], Generated.hostChunk058[8], Generated.hostChunk058[9], Generated.hostChunk058[10], Generated.hostChunk058[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0696_semantics
  · exact fixed_host_0697_semantics
  · exact fixed_host_0698_semantics
  · exact fixed_host_0699_semantics
  · exact fixed_host_0700_semantics
  · exact fixed_host_0701_semantics
  · exact fixed_host_0702_semantics
  · exact fixed_host_0703_semantics
  · exact fixed_host_0704_semantics
  · exact fixed_host_0705_semantics
  · exact fixed_host_0706_semantics
  · exact fixed_host_0707_semantics

end InducedPentagons.Paper

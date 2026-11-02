import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData061
import InducedPentagonsPaper.Generated.FixedRows053

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0732 :
    (fixedDensityCounts (maskGraph 7 58995), fixedComplementCounts (maskGraph 7 58995)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0732_semantics :
    ((Generated.hostChunk061[0]).induced.toList, (Generated.hostChunk061[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[0]).mask)) := by
  have hm : (Generated.hostChunk061[0]).mask = 58995 := by decide +kernel
  have hv : ((Generated.hostChunk061[0]).induced.toList, (Generated.hostChunk061[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0732]

theorem fixed_values_0733 :
    (fixedDensityCounts (maskGraph 7 58997), fixedComplementCounts (maskGraph 7 58997)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 5, 3, 0, 1, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0733_semantics :
    ((Generated.hostChunk061[1]).induced.toList, (Generated.hostChunk061[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[1]).mask)) := by
  have hm : (Generated.hostChunk061[1]).mask = 58997 := by decide +kernel
  have hv : ((Generated.hostChunk061[1]).induced.toList, (Generated.hostChunk061[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 5, 3, 0, 1, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0733]

theorem fixed_values_0734 :
    (fixedDensityCounts (maskGraph 7 58999), fixedComplementCounts (maskGraph 7 58999)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 4, 0, 0, 0, 2, 0, 0, 2, 2, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0734_semantics :
    ((Generated.hostChunk061[2]).induced.toList, (Generated.hostChunk061[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[2]).mask)) := by
  have hm : (Generated.hostChunk061[2]).mask = 58999 := by decide +kernel
  have hv : ((Generated.hostChunk061[2]).induced.toList, (Generated.hostChunk061[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 4, 0, 0, 0, 2, 0, 0, 2, 2, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0734]

theorem fixed_values_0735 :
    (fixedDensityCounts (maskGraph 7 59004), fixedComplementCounts (maskGraph 7 59004)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 4, 0, 0, 0, 0, 3, 8, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0735_semantics :
    ((Generated.hostChunk061[3]).induced.toList, (Generated.hostChunk061[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[3]).mask)) := by
  have hm : (Generated.hostChunk061[3]).mask = 59004 := by decide +kernel
  have hv : ((Generated.hostChunk061[3]).induced.toList, (Generated.hostChunk061[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 4, 0, 0, 0, 0, 3, 8, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0735]

theorem fixed_values_0736 :
    (fixedDensityCounts (maskGraph 7 59005), fixedComplementCounts (maskGraph 7 59005)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 2, 2, 0, 0, 0, 2, 3, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0736_semantics :
    ((Generated.hostChunk061[4]).induced.toList, (Generated.hostChunk061[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[4]).mask)) := by
  have hm : (Generated.hostChunk061[4]).mask = 59005 := by decide +kernel
  have hv : ((Generated.hostChunk061[4]).induced.toList, (Generated.hostChunk061[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 2, 2, 0, 0, 0, 2, 3, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0736]

theorem fixed_values_0737 :
    (fixedDensityCounts (maskGraph 7 59007), fixedComplementCounts (maskGraph 7 59007)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0737_semantics :
    ((Generated.hostChunk061[5]).induced.toList, (Generated.hostChunk061[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[5]).mask)) := by
  have hm : (Generated.hostChunk061[5]).mask = 59007 := by decide +kernel
  have hv : ((Generated.hostChunk061[5]).induced.toList, (Generated.hostChunk061[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0737]

theorem fixed_values_0738 :
    (fixedDensityCounts (maskGraph 7 59063), fixedComplementCounts (maskGraph 7 59063)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 4, 2, 1, 1, 1, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0738_semantics :
    ((Generated.hostChunk061[6]).induced.toList, (Generated.hostChunk061[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[6]).mask)) := by
  have hm : (Generated.hostChunk061[6]).mask = 59063 := by decide +kernel
  have hv : ((Generated.hostChunk061[6]).induced.toList, (Generated.hostChunk061[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 4, 2, 1, 1, 1, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0738]

theorem fixed_values_0739 :
    (fixedDensityCounts (maskGraph 7 59065), fixedComplementCounts (maskGraph 7 59065)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 4, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0739_semantics :
    ((Generated.hostChunk061[7]).induced.toList, (Generated.hostChunk061[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[7]).mask)) := by
  have hm : (Generated.hostChunk061[7]).mask = 59065 := by decide +kernel
  have hv : ((Generated.hostChunk061[7]).induced.toList, (Generated.hostChunk061[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 4, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0739]

theorem fixed_values_0740 :
    (fixedDensityCounts (maskGraph 7 59066), fixedComplementCounts (maskGraph 7 59066)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 3, 2, 3, 1, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0740_semantics :
    ((Generated.hostChunk061[8]).induced.toList, (Generated.hostChunk061[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[8]).mask)) := by
  have hm : (Generated.hostChunk061[8]).mask = 59066 := by decide +kernel
  have hv : ((Generated.hostChunk061[8]).induced.toList, (Generated.hostChunk061[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 3, 2, 3, 1, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0740]

theorem fixed_values_0741 :
    (fixedDensityCounts (maskGraph 7 59067), fixedComplementCounts (maskGraph 7 59067)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 2, 0, 2, 5, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0741_semantics :
    ((Generated.hostChunk061[9]).induced.toList, (Generated.hostChunk061[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[9]).mask)) := by
  have hm : (Generated.hostChunk061[9]).mask = 59067 := by decide +kernel
  have hv : ((Generated.hostChunk061[9]).induced.toList, (Generated.hostChunk061[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 2, 0, 2, 5, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0741]

theorem fixed_values_0742 :
    (fixedDensityCounts (maskGraph 7 59069), fixedComplementCounts (maskGraph 7 59069)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 3, 1, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0742_semantics :
    ((Generated.hostChunk061[10]).induced.toList, (Generated.hostChunk061[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[10]).mask)) := by
  have hm : (Generated.hostChunk061[10]).mask = 59069 := by decide +kernel
  have hv : ((Generated.hostChunk061[10]).induced.toList, (Generated.hostChunk061[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 3, 1, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0742]

theorem fixed_values_0743 :
    (fixedDensityCounts (maskGraph 7 59070), fixedComplementCounts (maskGraph 7 59070)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 3, 2, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0743_semantics :
    ((Generated.hostChunk061[11]).induced.toList, (Generated.hostChunk061[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk061[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk061[11]).mask)) := by
  have hm : (Generated.hostChunk061[11]).mask = 59070 := by decide +kernel
  have hv : ((Generated.hostChunk061[11]).induced.toList, (Generated.hostChunk061[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 3, 2, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0743]

theorem fixed_chunk_061_semantics :
    ∀ h ∈ Generated.hostChunk061.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk061.toList = [Generated.hostChunk061[0], Generated.hostChunk061[1], Generated.hostChunk061[2], Generated.hostChunk061[3], Generated.hostChunk061[4], Generated.hostChunk061[5], Generated.hostChunk061[6], Generated.hostChunk061[7], Generated.hostChunk061[8], Generated.hostChunk061[9], Generated.hostChunk061[10], Generated.hostChunk061[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0732_semantics
  · exact fixed_host_0733_semantics
  · exact fixed_host_0734_semantics
  · exact fixed_host_0735_semantics
  · exact fixed_host_0736_semantics
  · exact fixed_host_0737_semantics
  · exact fixed_host_0738_semantics
  · exact fixed_host_0739_semantics
  · exact fixed_host_0740_semantics
  · exact fixed_host_0741_semantics
  · exact fixed_host_0742_semantics
  · exact fixed_host_0743_semantics

end InducedPentagons.Paper

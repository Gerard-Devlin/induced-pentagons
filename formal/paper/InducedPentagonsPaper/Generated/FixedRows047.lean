import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData047
import InducedPentagonsPaper.Generated.FixedRows039

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0564 :
    (fixedDensityCounts (maskGraph 7 44013), fixedComplementCounts (maskGraph 7 44013)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0564_semantics :
    ((Generated.hostChunk047[0]).induced.toList, (Generated.hostChunk047[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[0]).mask)) := by
  have hm : (Generated.hostChunk047[0]).mask = 44013 := by decide +kernel
  have hv : ((Generated.hostChunk047[0]).induced.toList, (Generated.hostChunk047[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0564]

theorem fixed_values_0565 :
    (fixedDensityCounts (maskGraph 7 44014), fixedComplementCounts (maskGraph 7 44014)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 2, 2, 1, 1, 1, 0, 0, 0, 0, 1, 4, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0565_semantics :
    ((Generated.hostChunk047[1]).induced.toList, (Generated.hostChunk047[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[1]).mask)) := by
  have hm : (Generated.hostChunk047[1]).mask = 44014 := by decide +kernel
  have hv : ((Generated.hostChunk047[1]).induced.toList, (Generated.hostChunk047[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 2, 2, 1, 1, 1, 0, 0, 0, 0, 1, 4, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0565]

theorem fixed_values_0566 :
    (fixedDensityCounts (maskGraph 7 44015), fixedComplementCounts (maskGraph 7 44015)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 2, 0, 3, 0, 2, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0566_semantics :
    ((Generated.hostChunk047[2]).induced.toList, (Generated.hostChunk047[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[2]).mask)) := by
  have hm : (Generated.hostChunk047[2]).mask = 44015 := by decide +kernel
  have hv : ((Generated.hostChunk047[2]).induced.toList, (Generated.hostChunk047[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 2, 0, 3, 0, 2, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0566]

theorem fixed_values_0567 :
    (fixedDensityCounts (maskGraph 7 44024), fixedComplementCounts (maskGraph 7 44024)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 4, 0, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0567_semantics :
    ((Generated.hostChunk047[3]).induced.toList, (Generated.hostChunk047[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[3]).mask)) := by
  have hm : (Generated.hostChunk047[3]).mask = 44024 := by decide +kernel
  have hv : ((Generated.hostChunk047[3]).induced.toList, (Generated.hostChunk047[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 4, 0, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0567]

theorem fixed_values_0568 :
    (fixedDensityCounts (maskGraph 7 44025), fixedComplementCounts (maskGraph 7 44025)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0568_semantics :
    ((Generated.hostChunk047[4]).induced.toList, (Generated.hostChunk047[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[4]).mask)) := by
  have hm : (Generated.hostChunk047[4]).mask = 44025 := by decide +kernel
  have hv : ((Generated.hostChunk047[4]).induced.toList, (Generated.hostChunk047[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0568]

theorem fixed_values_0569 :
    (fixedDensityCounts (maskGraph 7 44026), fixedComplementCounts (maskGraph 7 44026)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 2, 1, 1, 3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0569_semantics :
    ((Generated.hostChunk047[5]).induced.toList, (Generated.hostChunk047[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[5]).mask)) := by
  have hm : (Generated.hostChunk047[5]).mask = 44026 := by decide +kernel
  have hv : ((Generated.hostChunk047[5]).induced.toList, (Generated.hostChunk047[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 2, 1, 1, 3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0569]

theorem fixed_values_0570 :
    (fixedDensityCounts (maskGraph 7 44027), fixedComplementCounts (maskGraph 7 44027)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 2, 0, 2, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0570_semantics :
    ((Generated.hostChunk047[6]).induced.toList, (Generated.hostChunk047[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[6]).mask)) := by
  have hm : (Generated.hostChunk047[6]).mask = 44027 := by decide +kernel
  have hv : ((Generated.hostChunk047[6]).induced.toList, (Generated.hostChunk047[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 2, 0, 2, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0570]

theorem fixed_values_0571 :
    (fixedDensityCounts (maskGraph 7 44030), fixedComplementCounts (maskGraph 7 44030)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 0, 0, 3, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0571_semantics :
    ((Generated.hostChunk047[7]).induced.toList, (Generated.hostChunk047[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[7]).mask)) := by
  have hm : (Generated.hostChunk047[7]).mask = 44030 := by decide +kernel
  have hv : ((Generated.hostChunk047[7]).induced.toList, (Generated.hostChunk047[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 0, 0, 3, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0571]

theorem fixed_values_0572 :
    (fixedDensityCounts (maskGraph 7 44031), fixedComplementCounts (maskGraph 7 44031)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0572_semantics :
    ((Generated.hostChunk047[8]).induced.toList, (Generated.hostChunk047[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[8]).mask)) := by
  have hm : (Generated.hostChunk047[8]).mask = 44031 := by decide +kernel
  have hv : ((Generated.hostChunk047[8]).induced.toList, (Generated.hostChunk047[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0572]

theorem fixed_values_0573 :
    (fixedDensityCounts (maskGraph 7 44280), fixedComplementCounts (maskGraph 7 44280)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0573_semantics :
    ((Generated.hostChunk047[9]).induced.toList, (Generated.hostChunk047[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[9]).mask)) := by
  have hm : (Generated.hostChunk047[9]).mask = 44280 := by decide +kernel
  have hv : ((Generated.hostChunk047[9]).induced.toList, (Generated.hostChunk047[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0573]

theorem fixed_values_0574 :
    (fixedDensityCounts (maskGraph 7 44281), fixedComplementCounts (maskGraph 7 44281)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 1, 0, 0, 2, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0574_semantics :
    ((Generated.hostChunk047[10]).induced.toList, (Generated.hostChunk047[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[10]).mask)) := by
  have hm : (Generated.hostChunk047[10]).mask = 44281 := by decide +kernel
  have hv : ((Generated.hostChunk047[10]).induced.toList, (Generated.hostChunk047[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 1, 0, 0, 2, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0574]

theorem fixed_values_0575 :
    (fixedDensityCounts (maskGraph 7 44283), fixedComplementCounts (maskGraph 7 44283)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 0, 5, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0575_semantics :
    ((Generated.hostChunk047[11]).induced.toList, (Generated.hostChunk047[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk047[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk047[11]).mask)) := by
  have hm : (Generated.hostChunk047[11]).mask = 44283 := by decide +kernel
  have hv : ((Generated.hostChunk047[11]).induced.toList, (Generated.hostChunk047[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 0, 5, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0575]

theorem fixed_chunk_047_semantics :
    ∀ h ∈ Generated.hostChunk047.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk047.toList = [Generated.hostChunk047[0], Generated.hostChunk047[1], Generated.hostChunk047[2], Generated.hostChunk047[3], Generated.hostChunk047[4], Generated.hostChunk047[5], Generated.hostChunk047[6], Generated.hostChunk047[7], Generated.hostChunk047[8], Generated.hostChunk047[9], Generated.hostChunk047[10], Generated.hostChunk047[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0564_semantics
  · exact fixed_host_0565_semantics
  · exact fixed_host_0566_semantics
  · exact fixed_host_0567_semantics
  · exact fixed_host_0568_semantics
  · exact fixed_host_0569_semantics
  · exact fixed_host_0570_semantics
  · exact fixed_host_0571_semantics
  · exact fixed_host_0572_semantics
  · exact fixed_host_0573_semantics
  · exact fixed_host_0574_semantics
  · exact fixed_host_0575_semantics

end InducedPentagons.Paper

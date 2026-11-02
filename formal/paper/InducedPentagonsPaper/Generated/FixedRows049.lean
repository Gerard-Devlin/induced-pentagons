import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData049
import InducedPentagonsPaper.Generated.FixedRows041

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0588 :
    (fixedDensityCounts (maskGraph 7 44404), fixedComplementCounts (maskGraph 7 44404)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0588_semantics :
    ((Generated.hostChunk049[0]).induced.toList, (Generated.hostChunk049[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[0]).mask)) := by
  have hm : (Generated.hostChunk049[0]).mask = 44404 := by decide +kernel
  have hv : ((Generated.hostChunk049[0]).induced.toList, (Generated.hostChunk049[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0588]

theorem fixed_values_0589 :
    (fixedDensityCounts (maskGraph 7 44405), fixedComplementCounts (maskGraph 7 44405)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 2, 0, 0, 0, 1, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0589_semantics :
    ((Generated.hostChunk049[1]).induced.toList, (Generated.hostChunk049[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[1]).mask)) := by
  have hm : (Generated.hostChunk049[1]).mask = 44405 := by decide +kernel
  have hv : ((Generated.hostChunk049[1]).induced.toList, (Generated.hostChunk049[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 2, 0, 0, 0, 1, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0589]

theorem fixed_values_0590 :
    (fixedDensityCounts (maskGraph 7 44406), fixedComplementCounts (maskGraph 7 44406)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 4, 0, 0, 0, 2, 1, 3, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0590_semantics :
    ((Generated.hostChunk049[2]).induced.toList, (Generated.hostChunk049[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[2]).mask)) := by
  have hm : (Generated.hostChunk049[2]).mask = 44406 := by decide +kernel
  have hv : ((Generated.hostChunk049[2]).induced.toList, (Generated.hostChunk049[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 4, 0, 0, 0, 2, 1, 3, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0590]

theorem fixed_values_0591 :
    (fixedDensityCounts (maskGraph 7 44407), fixedComplementCounts (maskGraph 7 44407)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 1, 0, 0, 0, 2, 3, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0591_semantics :
    ((Generated.hostChunk049[3]).induced.toList, (Generated.hostChunk049[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[3]).mask)) := by
  have hm : (Generated.hostChunk049[3]).mask = 44407 := by decide +kernel
  have hv : ((Generated.hostChunk049[3]).induced.toList, (Generated.hostChunk049[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 1, 0, 0, 0, 2, 3, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0591]

theorem fixed_values_0592 :
    (fixedDensityCounts (maskGraph 7 44412), fixedComplementCounts (maskGraph 7 44412)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 1, 0, 0, 0, 2, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0592_semantics :
    ((Generated.hostChunk049[4]).induced.toList, (Generated.hostChunk049[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[4]).mask)) := by
  have hm : (Generated.hostChunk049[4]).mask = 44412 := by decide +kernel
  have hv : ((Generated.hostChunk049[4]).induced.toList, (Generated.hostChunk049[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 1, 0, 0, 0, 2, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0592]

theorem fixed_values_0593 :
    (fixedDensityCounts (maskGraph 7 44413), fixedComplementCounts (maskGraph 7 44413)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 2, 0, 0, 0, 1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0593_semantics :
    ((Generated.hostChunk049[5]).induced.toList, (Generated.hostChunk049[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[5]).mask)) := by
  have hm : (Generated.hostChunk049[5]).mask = 44413 := by decide +kernel
  have hv : ((Generated.hostChunk049[5]).induced.toList, (Generated.hostChunk049[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 2, 0, 0, 0, 1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0593]

theorem fixed_values_0594 :
    (fixedDensityCounts (maskGraph 7 44415), fixedComplementCounts (maskGraph 7 44415)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 3, 0, 0, 0, 0, 2, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0594_semantics :
    ((Generated.hostChunk049[6]).induced.toList, (Generated.hostChunk049[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[6]).mask)) := by
  have hm : (Generated.hostChunk049[6]).mask = 44415 := by decide +kernel
  have hv : ((Generated.hostChunk049[6]).induced.toList, (Generated.hostChunk049[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 3, 0, 0, 0, 0, 2, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0594]

theorem fixed_values_0595 :
    (fixedDensityCounts (maskGraph 7 44460), fixedComplementCounts (maskGraph 7 44460)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 1, 0, 3, 1, 2, 2, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0595_semantics :
    ((Generated.hostChunk049[7]).induced.toList, (Generated.hostChunk049[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[7]).mask)) := by
  have hm : (Generated.hostChunk049[7]).mask = 44460 := by decide +kernel
  have hv : ((Generated.hostChunk049[7]).induced.toList, (Generated.hostChunk049[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 1, 0, 3, 1, 2, 2, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0595]

theorem fixed_values_0596 :
    (fixedDensityCounts (maskGraph 7 44461), fixedComplementCounts (maskGraph 7 44461)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 3, 2, 2, 0, 0, 0, 0, 1, 2, 3, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0596_semantics :
    ((Generated.hostChunk049[8]).induced.toList, (Generated.hostChunk049[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[8]).mask)) := by
  have hm : (Generated.hostChunk049[8]).mask = 44461 := by decide +kernel
  have hv : ((Generated.hostChunk049[8]).induced.toList, (Generated.hostChunk049[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 3, 2, 2, 0, 0, 0, 0, 1, 2, 3, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0596]

theorem fixed_values_0597 :
    (fixedDensityCounts (maskGraph 7 44462), fixedComplementCounts (maskGraph 7 44462)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 2, 1, 3, 3, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0597_semantics :
    ((Generated.hostChunk049[9]).induced.toList, (Generated.hostChunk049[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[9]).mask)) := by
  have hm : (Generated.hostChunk049[9]).mask = 44462 := by decide +kernel
  have hv : ((Generated.hostChunk049[9]).induced.toList, (Generated.hostChunk049[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 2, 1, 3, 3, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0597]

theorem fixed_values_0598 :
    (fixedDensityCounts (maskGraph 7 44463), fixedComplementCounts (maskGraph 7 44463)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 2, 1, 2, 0, 2, 0, 0, 1, 0, 3, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0598_semantics :
    ((Generated.hostChunk049[10]).induced.toList, (Generated.hostChunk049[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[10]).mask)) := by
  have hm : (Generated.hostChunk049[10]).mask = 44463 := by decide +kernel
  have hv : ((Generated.hostChunk049[10]).induced.toList, (Generated.hostChunk049[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 2, 1, 2, 0, 2, 0, 0, 1, 0, 3, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0598]

theorem fixed_values_0599 :
    (fixedDensityCounts (maskGraph 7 44466), fixedComplementCounts (maskGraph 7 44466)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 2, 6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0599_semantics :
    ((Generated.hostChunk049[11]).induced.toList, (Generated.hostChunk049[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk049[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk049[11]).mask)) := by
  have hm : (Generated.hostChunk049[11]).mask = 44466 := by decide +kernel
  have hv : ((Generated.hostChunk049[11]).induced.toList, (Generated.hostChunk049[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 2, 6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0599]

theorem fixed_chunk_049_semantics :
    ∀ h ∈ Generated.hostChunk049.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk049.toList = [Generated.hostChunk049[0], Generated.hostChunk049[1], Generated.hostChunk049[2], Generated.hostChunk049[3], Generated.hostChunk049[4], Generated.hostChunk049[5], Generated.hostChunk049[6], Generated.hostChunk049[7], Generated.hostChunk049[8], Generated.hostChunk049[9], Generated.hostChunk049[10], Generated.hostChunk049[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0588_semantics
  · exact fixed_host_0589_semantics
  · exact fixed_host_0590_semantics
  · exact fixed_host_0591_semantics
  · exact fixed_host_0592_semantics
  · exact fixed_host_0593_semantics
  · exact fixed_host_0594_semantics
  · exact fixed_host_0595_semantics
  · exact fixed_host_0596_semantics
  · exact fixed_host_0597_semantics
  · exact fixed_host_0598_semantics
  · exact fixed_host_0599_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData041
import InducedPentagonsPaper.Generated.FixedRows033

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0492 :
    (fixedDensityCounts (maskGraph 7 42099), fixedComplementCounts (maskGraph 7 42099)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 4, 5, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0492_semantics :
    ((Generated.hostChunk041[0]).induced.toList, (Generated.hostChunk041[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[0]).mask)) := by
  have hm : (Generated.hostChunk041[0]).mask = 42099 := by decide +kernel
  have hv : ((Generated.hostChunk041[0]).induced.toList, (Generated.hostChunk041[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 4, 5, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0492]

theorem fixed_values_0493 :
    (fixedDensityCounts (maskGraph 7 42100), fixedComplementCounts (maskGraph 7 42100)) =
      ([0, 0, 0, 0, 0, 0, 2, 8, 0, 3, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0493_semantics :
    ((Generated.hostChunk041[1]).induced.toList, (Generated.hostChunk041[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[1]).mask)) := by
  have hm : (Generated.hostChunk041[1]).mask = 42100 := by decide +kernel
  have hv : ((Generated.hostChunk041[1]).induced.toList, (Generated.hostChunk041[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 8, 0, 3, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0493]

theorem fixed_values_0494 :
    (fixedDensityCounts (maskGraph 7 42101), fixedComplementCounts (maskGraph 7 42101)) =
      ([0, 0, 0, 0, 0, 0, 2, 4, 2, 2, 3, 1, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0494_semantics :
    ((Generated.hostChunk041[2]).induced.toList, (Generated.hostChunk041[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[2]).mask)) := by
  have hm : (Generated.hostChunk041[2]).mask = 42101 := by decide +kernel
  have hv : ((Generated.hostChunk041[2]).induced.toList, (Generated.hostChunk041[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 4, 2, 2, 3, 1, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0494]

theorem fixed_values_0495 :
    (fixedDensityCounts (maskGraph 7 42103), fixedComplementCounts (maskGraph 7 42103)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 3, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0495_semantics :
    ((Generated.hostChunk041[3]).induced.toList, (Generated.hostChunk041[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[3]).mask)) := by
  have hm : (Generated.hostChunk041[3]).mask = 42103 := by decide +kernel
  have hv : ((Generated.hostChunk041[3]).induced.toList, (Generated.hostChunk041[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 3, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0495]

theorem fixed_values_0496 :
    (fixedDensityCounts (maskGraph 7 42108), fixedComplementCounts (maskGraph 7 42108)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 4, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0496_semantics :
    ((Generated.hostChunk041[4]).induced.toList, (Generated.hostChunk041[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[4]).mask)) := by
  have hm : (Generated.hostChunk041[4]).mask = 42108 := by decide +kernel
  have hv : ((Generated.hostChunk041[4]).induced.toList, (Generated.hostChunk041[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 4, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0496]

theorem fixed_values_0497 :
    (fixedDensityCounts (maskGraph 7 42109), fixedComplementCounts (maskGraph 7 42109)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 2, 4, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0497_semantics :
    ((Generated.hostChunk041[5]).induced.toList, (Generated.hostChunk041[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[5]).mask)) := by
  have hm : (Generated.hostChunk041[5]).mask = 42109 := by decide +kernel
  have hv : ((Generated.hostChunk041[5]).induced.toList, (Generated.hostChunk041[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 2, 4, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0497]

theorem fixed_values_0498 :
    (fixedDensityCounts (maskGraph 7 42111), fixedComplementCounts (maskGraph 7 42111)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 7, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0498_semantics :
    ((Generated.hostChunk041[6]).induced.toList, (Generated.hostChunk041[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[6]).mask)) := by
  have hm : (Generated.hostChunk041[6]).mask = 42111 := by decide +kernel
  have hv : ((Generated.hostChunk041[6]).induced.toList, (Generated.hostChunk041[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 7, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0498]

theorem fixed_values_0499 :
    (fixedDensityCounts (maskGraph 7 42218), fixedComplementCounts (maskGraph 7 42218)) =
      ([0, 0, 0, 0, 0, 0, 1, 7, 0, 0, 6, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0499_semantics :
    ((Generated.hostChunk041[7]).induced.toList, (Generated.hostChunk041[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[7]).mask)) := by
  have hm : (Generated.hostChunk041[7]).mask = 42218 := by decide +kernel
  have hv : ((Generated.hostChunk041[7]).induced.toList, (Generated.hostChunk041[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 7, 0, 0, 6, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0499]

theorem fixed_values_0500 :
    (fixedDensityCounts (maskGraph 7 42219), fixedComplementCounts (maskGraph 7 42219)) =
      ([0, 0, 0, 0, 0, 0, 1, 4, 2, 0, 4, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0500_semantics :
    ((Generated.hostChunk041[8]).induced.toList, (Generated.hostChunk041[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[8]).mask)) := by
  have hm : (Generated.hostChunk041[8]).mask = 42219 := by decide +kernel
  have hv : ((Generated.hostChunk041[8]).induced.toList, (Generated.hostChunk041[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 4, 2, 0, 4, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0500]

theorem fixed_values_0501 :
    (fixedDensityCounts (maskGraph 7 42220), fixedComplementCounts (maskGraph 7 42220)) =
      ([0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 2, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0501_semantics :
    ((Generated.hostChunk041[9]).induced.toList, (Generated.hostChunk041[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[9]).mask)) := by
  have hm : (Generated.hostChunk041[9]).mask = 42220 := by decide +kernel
  have hv : ((Generated.hostChunk041[9]).induced.toList, (Generated.hostChunk041[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 2, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0501]

theorem fixed_values_0502 :
    (fixedDensityCounts (maskGraph 7 42221), fixedComplementCounts (maskGraph 7 42221)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 2, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0502_semantics :
    ((Generated.hostChunk041[10]).induced.toList, (Generated.hostChunk041[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[10]).mask)) := by
  have hm : (Generated.hostChunk041[10]).mask = 42221 := by decide +kernel
  have hv : ((Generated.hostChunk041[10]).induced.toList, (Generated.hostChunk041[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 2, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0502]

theorem fixed_values_0503 :
    (fixedDensityCounts (maskGraph 7 42222), fixedComplementCounts (maskGraph 7 42222)) =
      ([0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 5, 1, 1, 0, 1, 0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0503_semantics :
    ((Generated.hostChunk041[11]).induced.toList, (Generated.hostChunk041[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk041[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk041[11]).mask)) := by
  have hm : (Generated.hostChunk041[11]).mask = 42222 := by decide +kernel
  have hv : ((Generated.hostChunk041[11]).induced.toList, (Generated.hostChunk041[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 5, 1, 1, 0, 1, 0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0503]

theorem fixed_chunk_041_semantics :
    ∀ h ∈ Generated.hostChunk041.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk041.toList = [Generated.hostChunk041[0], Generated.hostChunk041[1], Generated.hostChunk041[2], Generated.hostChunk041[3], Generated.hostChunk041[4], Generated.hostChunk041[5], Generated.hostChunk041[6], Generated.hostChunk041[7], Generated.hostChunk041[8], Generated.hostChunk041[9], Generated.hostChunk041[10], Generated.hostChunk041[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0492_semantics
  · exact fixed_host_0493_semantics
  · exact fixed_host_0494_semantics
  · exact fixed_host_0495_semantics
  · exact fixed_host_0496_semantics
  · exact fixed_host_0497_semantics
  · exact fixed_host_0498_semantics
  · exact fixed_host_0499_semantics
  · exact fixed_host_0500_semantics
  · exact fixed_host_0501_semantics
  · exact fixed_host_0502_semantics
  · exact fixed_host_0503_semantics

end InducedPentagons.Paper

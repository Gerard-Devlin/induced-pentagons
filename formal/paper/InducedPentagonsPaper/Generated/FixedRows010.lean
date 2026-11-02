import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData010
import InducedPentagonsPaper.Generated.FixedRows002

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0120 :
    (fixedDensityCounts (maskGraph 7 2551), fixedComplementCounts (maskGraph 7 2551)) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 4, 0, 1, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0120_semantics :
    ((Generated.hostChunk010[0]).induced.toList, (Generated.hostChunk010[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[0]).mask)) := by
  have hm : (Generated.hostChunk010[0]).mask = 2551 := by decide +kernel
  have hv : ((Generated.hostChunk010[0]).induced.toList, (Generated.hostChunk010[0]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 4, 0, 1, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0120]

theorem fixed_values_0121 :
    (fixedDensityCounts (maskGraph 7 2552), fixedComplementCounts (maskGraph 7 2552)) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 2, 5, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0121_semantics :
    ((Generated.hostChunk010[1]).induced.toList, (Generated.hostChunk010[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[1]).mask)) := by
  have hm : (Generated.hostChunk010[1]).mask = 2552 := by decide +kernel
  have hv : ((Generated.hostChunk010[1]).induced.toList, (Generated.hostChunk010[1]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 2, 5, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0121]

theorem fixed_values_0122 :
    (fixedDensityCounts (maskGraph 7 2553), fixedComplementCounts (maskGraph 7 2553)) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 2, 3, 2, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 1, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0122_semantics :
    ((Generated.hostChunk010[2]).induced.toList, (Generated.hostChunk010[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[2]).mask)) := by
  have hm : (Generated.hostChunk010[2]).mask = 2553 := by decide +kernel
  have hv : ((Generated.hostChunk010[2]).induced.toList, (Generated.hostChunk010[2]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 0, 0, 2, 3, 2, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 1, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0122]

theorem fixed_values_0123 :
    (fixedDensityCounts (maskGraph 7 2554), fixedComplementCounts (maskGraph 7 2554)) =
      ([0, 1, 2, 1, 1, 1, 0, 0, 2, 1, 5, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0123_semantics :
    ((Generated.hostChunk010[3]).induced.toList, (Generated.hostChunk010[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[3]).mask)) := by
  have hm : (Generated.hostChunk010[3]).mask = 2554 := by decide +kernel
  have hv : ((Generated.hostChunk010[3]).induced.toList, (Generated.hostChunk010[3]).complement.toList) =
      ([0, 1, 2, 1, 1, 1, 0, 0, 2, 1, 5, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0123]

theorem fixed_values_0124 :
    (fixedDensityCounts (maskGraph 7 2555), fixedComplementCounts (maskGraph 7 2555)) =
      ([0, 1, 2, 1, 1, 1, 0, 0, 2, 0, 4, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 1, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0124_semantics :
    ((Generated.hostChunk010[4]).induced.toList, (Generated.hostChunk010[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[4]).mask)) := by
  have hm : (Generated.hostChunk010[4]).mask = 2555 := by decide +kernel
  have hv : ((Generated.hostChunk010[4]).induced.toList, (Generated.hostChunk010[4]).complement.toList) =
      ([0, 1, 2, 1, 1, 1, 0, 0, 2, 0, 4, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 1, 1, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0124]

theorem fixed_values_0125 :
    (fixedDensityCounts (maskGraph 7 2558), fixedComplementCounts (maskGraph 7 2558)) =
      ([0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 3, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 2, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0125_semantics :
    ((Generated.hostChunk010[5]).induced.toList, (Generated.hostChunk010[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[5]).mask)) := by
  have hm : (Generated.hostChunk010[5]).mask = 2558 := by decide +kernel
  have hv : ((Generated.hostChunk010[5]).induced.toList, (Generated.hostChunk010[5]).complement.toList) =
      ([0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 3, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 2, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0125]

theorem fixed_values_0126 :
    (fixedDensityCounts (maskGraph 7 2559), fixedComplementCounts (maskGraph 7 2559)) =
      ([0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0126_semantics :
    ((Generated.hostChunk010[6]).induced.toList, (Generated.hostChunk010[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[6]).mask)) := by
  have hm : (Generated.hostChunk010[6]).mask = 2559 := by decide +kernel
  have hv : ((Generated.hostChunk010[6]).induced.toList, (Generated.hostChunk010[6]).complement.toList) =
      ([0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0126]

theorem fixed_values_0127 :
    (fixedDensityCounts (maskGraph 7 2840), fixedComplementCounts (maskGraph 7 2840)) =
      ([0, 2, 8, 0, 0, 0, 4, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0127_semantics :
    ((Generated.hostChunk010[7]).induced.toList, (Generated.hostChunk010[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[7]).mask)) := by
  have hm : (Generated.hostChunk010[7]).mask = 2840 := by decide +kernel
  have hv : ((Generated.hostChunk010[7]).induced.toList, (Generated.hostChunk010[7]).complement.toList) =
      ([0, 2, 8, 0, 0, 0, 4, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0127]

theorem fixed_values_0128 :
    (fixedDensityCounts (maskGraph 7 2841), fixedComplementCounts (maskGraph 7 2841)) =
      ([0, 1, 4, 0, 0, 4, 5, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0128_semantics :
    ((Generated.hostChunk010[8]).induced.toList, (Generated.hostChunk010[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[8]).mask)) := by
  have hm : (Generated.hostChunk010[8]).mask = 2841 := by decide +kernel
  have hv : ((Generated.hostChunk010[8]).induced.toList, (Generated.hostChunk010[8]).complement.toList) =
      ([0, 1, 4, 0, 0, 4, 5, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0128]

theorem fixed_values_0129 :
    (fixedDensityCounts (maskGraph 7 2842), fixedComplementCounts (maskGraph 7 2842)) =
      ([0, 1, 6, 1, 0, 0, 2, 4, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0129_semantics :
    ((Generated.hostChunk010[9]).induced.toList, (Generated.hostChunk010[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[9]).mask)) := by
  have hm : (Generated.hostChunk010[9]).mask = 2842 := by decide +kernel
  have hv : ((Generated.hostChunk010[9]).induced.toList, (Generated.hostChunk010[9]).complement.toList) =
      ([0, 1, 6, 1, 0, 0, 2, 4, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0129]

theorem fixed_values_0130 :
    (fixedDensityCounts (maskGraph 7 2843), fixedComplementCounts (maskGraph 7 2843)) =
      ([0, 1, 3, 1, 0, 2, 2, 3, 2, 1, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0130_semantics :
    ((Generated.hostChunk010[10]).induced.toList, (Generated.hostChunk010[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[10]).mask)) := by
  have hm : (Generated.hostChunk010[10]).mask = 2843 := by decide +kernel
  have hv : ((Generated.hostChunk010[10]).induced.toList, (Generated.hostChunk010[10]).complement.toList) =
      ([0, 1, 3, 1, 0, 2, 2, 3, 2, 1, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0130]

theorem fixed_values_0131 :
    (fixedDensityCounts (maskGraph 7 2846), fixedComplementCounts (maskGraph 7 2846)) =
      ([0, 1, 2, 2, 0, 1, 2, 4, 2, 1, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0131_semantics :
    ((Generated.hostChunk010[11]).induced.toList, (Generated.hostChunk010[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk010[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk010[11]).mask)) := by
  have hm : (Generated.hostChunk010[11]).mask = 2846 := by decide +kernel
  have hv : ((Generated.hostChunk010[11]).induced.toList, (Generated.hostChunk010[11]).complement.toList) =
      ([0, 1, 2, 2, 0, 1, 2, 4, 2, 1, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0131]

theorem fixed_chunk_010_semantics :
    ∀ h ∈ Generated.hostChunk010.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk010.toList = [Generated.hostChunk010[0], Generated.hostChunk010[1], Generated.hostChunk010[2], Generated.hostChunk010[3], Generated.hostChunk010[4], Generated.hostChunk010[5], Generated.hostChunk010[6], Generated.hostChunk010[7], Generated.hostChunk010[8], Generated.hostChunk010[9], Generated.hostChunk010[10], Generated.hostChunk010[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0120_semantics
  · exact fixed_host_0121_semantics
  · exact fixed_host_0122_semantics
  · exact fixed_host_0123_semantics
  · exact fixed_host_0124_semantics
  · exact fixed_host_0125_semantics
  · exact fixed_host_0126_semantics
  · exact fixed_host_0127_semantics
  · exact fixed_host_0128_semantics
  · exact fixed_host_0129_semantics
  · exact fixed_host_0130_semantics
  · exact fixed_host_0131_semantics

end InducedPentagons.Paper

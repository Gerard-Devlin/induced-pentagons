import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData078
import InducedPentagonsPaper.Generated.FixedRows070

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0936 :
    (fixedDensityCounts (maskGraph 7 262143), fixedComplementCounts (maskGraph 7 262143)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0]) := by
  decide +kernel

theorem fixed_host_0936_semantics :
    ((Generated.hostChunk078[0]).induced.toList, (Generated.hostChunk078[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[0]).mask)) := by
  have hm : (Generated.hostChunk078[0]).mask = 262143 := by decide +kernel
  have hv : ((Generated.hostChunk078[0]).induced.toList, (Generated.hostChunk078[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0936]

theorem fixed_values_0937 :
    (fixedDensityCounts (maskGraph 7 375775), fixedComplementCounts (maskGraph 7 375775)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0937_semantics :
    ((Generated.hostChunk078[1]).induced.toList, (Generated.hostChunk078[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[1]).mask)) := by
  have hm : (Generated.hostChunk078[1]).mask = 375775 := by decide +kernel
  have hv : ((Generated.hostChunk078[1]).induced.toList, (Generated.hostChunk078[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0937]

theorem fixed_values_0938 :
    (fixedDensityCounts (maskGraph 7 375776), fixedComplementCounts (maskGraph 7 375776)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0938_semantics :
    ((Generated.hostChunk078[2]).induced.toList, (Generated.hostChunk078[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[2]).mask)) := by
  have hm : (Generated.hostChunk078[2]).mask = 375776 := by decide +kernel
  have hv : ((Generated.hostChunk078[2]).induced.toList, (Generated.hostChunk078[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0938]

theorem fixed_values_0939 :
    (fixedDensityCounts (maskGraph 7 375777), fixedComplementCounts (maskGraph 7 375777)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0939_semantics :
    ((Generated.hostChunk078[3]).induced.toList, (Generated.hostChunk078[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[3]).mask)) := by
  have hm : (Generated.hostChunk078[3]).mask = 375777 := by decide +kernel
  have hv : ((Generated.hostChunk078[3]).induced.toList, (Generated.hostChunk078[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0939]

theorem fixed_values_0940 :
    (fixedDensityCounts (maskGraph 7 375779), fixedComplementCounts (maskGraph 7 375779)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 6, 3, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0940_semantics :
    ((Generated.hostChunk078[4]).induced.toList, (Generated.hostChunk078[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[4]).mask)) := by
  have hm : (Generated.hostChunk078[4]).mask = 375779 := by decide +kernel
  have hv : ((Generated.hostChunk078[4]).induced.toList, (Generated.hostChunk078[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 6, 3, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0940]

theorem fixed_values_0941 :
    (fixedDensityCounts (maskGraph 7 375783), fixedComplementCounts (maskGraph 7 375783)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 3, 6, 1, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0941_semantics :
    ((Generated.hostChunk078[5]).induced.toList, (Generated.hostChunk078[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[5]).mask)) := by
  have hm : (Generated.hostChunk078[5]).mask = 375783 := by decide +kernel
  have hv : ((Generated.hostChunk078[5]).induced.toList, (Generated.hostChunk078[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 3, 6, 1, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0941]

theorem fixed_values_0942 :
    (fixedDensityCounts (maskGraph 7 375791), fixedComplementCounts (maskGraph 7 375791)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 6, 4, 0, 0, 0, 0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0942_semantics :
    ((Generated.hostChunk078[6]).induced.toList, (Generated.hostChunk078[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[6]).mask)) := by
  have hm : (Generated.hostChunk078[6]).mask = 375791 := by decide +kernel
  have hv : ((Generated.hostChunk078[6]).induced.toList, (Generated.hostChunk078[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 6, 4, 0, 0, 0, 0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0942]

theorem fixed_values_0943 :
    (fixedDensityCounts (maskGraph 7 375807), fixedComplementCounts (maskGraph 7 375807)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0943_semantics :
    ((Generated.hostChunk078[7]).induced.toList, (Generated.hostChunk078[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[7]).mask)) := by
  have hm : (Generated.hostChunk078[7]).mask = 375807 := by decide +kernel
  have hv : ((Generated.hostChunk078[7]).induced.toList, (Generated.hostChunk078[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0943]

theorem fixed_values_0944 :
    (fixedDensityCounts (maskGraph 7 375841), fixedComplementCounts (maskGraph 7 375841)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0944_semantics :
    ((Generated.hostChunk078[8]).induced.toList, (Generated.hostChunk078[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[8]).mask)) := by
  have hm : (Generated.hostChunk078[8]).mask = 375841 := by decide +kernel
  have hv : ((Generated.hostChunk078[8]).induced.toList, (Generated.hostChunk078[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0944]

theorem fixed_values_0945 :
    (fixedDensityCounts (maskGraph 7 375843), fixedComplementCounts (maskGraph 7 375843)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 9, 9, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0945_semantics :
    ((Generated.hostChunk078[9]).induced.toList, (Generated.hostChunk078[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[9]).mask)) := by
  have hm : (Generated.hostChunk078[9]).mask = 375843 := by decide +kernel
  have hv : ((Generated.hostChunk078[9]).induced.toList, (Generated.hostChunk078[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 9, 9, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0945]

theorem fixed_values_0946 :
    (fixedDensityCounts (maskGraph 7 375847), fixedComplementCounts (maskGraph 7 375847)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 8, 4, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0946_semantics :
    ((Generated.hostChunk078[10]).induced.toList, (Generated.hostChunk078[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[10]).mask)) := by
  have hm : (Generated.hostChunk078[10]).mask = 375847 := by decide +kernel
  have hv : ((Generated.hostChunk078[10]).induced.toList, (Generated.hostChunk078[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 8, 4, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0946]

theorem fixed_values_0947 :
    (fixedDensityCounts (maskGraph 7 375855), fixedComplementCounts (maskGraph 7 375855)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3, 6, 2, 3, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0947_semantics :
    ((Generated.hostChunk078[11]).induced.toList, (Generated.hostChunk078[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk078[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk078[11]).mask)) := by
  have hm : (Generated.hostChunk078[11]).mask = 375855 := by decide +kernel
  have hv : ((Generated.hostChunk078[11]).induced.toList, (Generated.hostChunk078[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3, 6, 2, 3, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0947]

theorem fixed_chunk_078_semantics :
    ∀ h ∈ Generated.hostChunk078.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk078.toList = [Generated.hostChunk078[0], Generated.hostChunk078[1], Generated.hostChunk078[2], Generated.hostChunk078[3], Generated.hostChunk078[4], Generated.hostChunk078[5], Generated.hostChunk078[6], Generated.hostChunk078[7], Generated.hostChunk078[8], Generated.hostChunk078[9], Generated.hostChunk078[10], Generated.hostChunk078[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0936_semantics
  · exact fixed_host_0937_semantics
  · exact fixed_host_0938_semantics
  · exact fixed_host_0939_semantics
  · exact fixed_host_0940_semantics
  · exact fixed_host_0941_semantics
  · exact fixed_host_0942_semantics
  · exact fixed_host_0943_semantics
  · exact fixed_host_0944_semantics
  · exact fixed_host_0945_semantics
  · exact fixed_host_0946_semantics
  · exact fixed_host_0947_semantics

end InducedPentagons.Paper

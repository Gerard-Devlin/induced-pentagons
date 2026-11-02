import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData032
import InducedPentagonsPaper.Generated.FixedRows024

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0384 :
    (fixedDensityCounts (maskGraph 7 39479), fixedComplementCounts (maskGraph 7 39479)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 1, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0384_semantics :
    ((Generated.hostChunk032[0]).induced.toList, (Generated.hostChunk032[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[0]).mask)) := by
  have hm : (Generated.hostChunk032[0]).mask = 39479 := by decide +kernel
  have hv : ((Generated.hostChunk032[0]).induced.toList, (Generated.hostChunk032[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 1, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0384]

theorem fixed_values_0385 :
    (fixedDensityCounts (maskGraph 7 39487), fixedComplementCounts (maskGraph 7 39487)) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0385_semantics :
    ((Generated.hostChunk032[1]).induced.toList, (Generated.hostChunk032[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[1]).mask)) := by
  have hm : (Generated.hostChunk032[1]).mask = 39487 := by decide +kernel
  have hv : ((Generated.hostChunk032[1]).induced.toList, (Generated.hostChunk032[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0385]

theorem fixed_values_0386 :
    (fixedDensityCounts (maskGraph 7 39509), fixedComplementCounts (maskGraph 7 39509)) =
      ([0, 0, 0, 0, 0, 2, 2, 6, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0386_semantics :
    ((Generated.hostChunk032[2]).induced.toList, (Generated.hostChunk032[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[2]).mask)) := by
  have hm : (Generated.hostChunk032[2]).mask = 39509 := by decide +kernel
  have hv : ((Generated.hostChunk032[2]).induced.toList, (Generated.hostChunk032[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 2, 6, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0386]

theorem fixed_values_0387 :
    (fixedDensityCounts (maskGraph 7 39511), fixedComplementCounts (maskGraph 7 39511)) =
      ([0, 0, 0, 0, 0, 2, 1, 5, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0387_semantics :
    ((Generated.hostChunk032[3]).induced.toList, (Generated.hostChunk032[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[3]).mask)) := by
  have hm : (Generated.hostChunk032[3]).mask = 39511 := by decide +kernel
  have hv : ((Generated.hostChunk032[3]).induced.toList, (Generated.hostChunk032[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 1, 5, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0387]

theorem fixed_values_0388 :
    (fixedDensityCounts (maskGraph 7 39516), fixedComplementCounts (maskGraph 7 39516)) =
      ([0, 0, 0, 0, 0, 2, 1, 9, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0388_semantics :
    ((Generated.hostChunk032[4]).induced.toList, (Generated.hostChunk032[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[4]).mask)) := by
  have hm : (Generated.hostChunk032[4]).mask = 39516 := by decide +kernel
  have hv : ((Generated.hostChunk032[4]).induced.toList, (Generated.hostChunk032[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 1, 9, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0388]

theorem fixed_values_0389 :
    (fixedDensityCounts (maskGraph 7 39517), fixedComplementCounts (maskGraph 7 39517)) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 6, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0389_semantics :
    ((Generated.hostChunk032[5]).induced.toList, (Generated.hostChunk032[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[5]).mask)) := by
  have hm : (Generated.hostChunk032[5]).mask = 39517 := by decide +kernel
  have hv : ((Generated.hostChunk032[5]).induced.toList, (Generated.hostChunk032[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 6, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0389]

theorem fixed_values_0390 :
    (fixedDensityCounts (maskGraph 7 39518), fixedComplementCounts (maskGraph 7 39518)) =
      ([0, 0, 0, 0, 0, 2, 1, 4, 6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0390_semantics :
    ((Generated.hostChunk032[6]).induced.toList, (Generated.hostChunk032[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[6]).mask)) := by
  have hm : (Generated.hostChunk032[6]).mask = 39518 := by decide +kernel
  have hv : ((Generated.hostChunk032[6]).induced.toList, (Generated.hostChunk032[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 1, 4, 6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0390]

theorem fixed_values_0391 :
    (fixedDensityCounts (maskGraph 7 39519), fixedComplementCounts (maskGraph 7 39519)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 7, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0391_semantics :
    ((Generated.hostChunk032[7]).induced.toList, (Generated.hostChunk032[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[7]).mask)) := by
  have hm : (Generated.hostChunk032[7]).mask = 39519 := by decide +kernel
  have hv : ((Generated.hostChunk032[7]).induced.toList, (Generated.hostChunk032[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 7, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0391]

theorem fixed_values_0392 :
    (fixedDensityCounts (maskGraph 7 39522), fixedComplementCounts (maskGraph 7 39522)) =
      ([0, 0, 0, 0, 0, 1, 6, 4, 2, 0, 4, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0392_semantics :
    ((Generated.hostChunk032[8]).induced.toList, (Generated.hostChunk032[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[8]).mask)) := by
  have hm : (Generated.hostChunk032[8]).mask = 39522 := by decide +kernel
  have hv : ((Generated.hostChunk032[8]).induced.toList, (Generated.hostChunk032[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 6, 4, 2, 0, 4, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0392]

theorem fixed_values_0393 :
    (fixedDensityCounts (maskGraph 7 39523), fixedComplementCounts (maskGraph 7 39523)) =
      ([0, 0, 0, 0, 0, 1, 2, 6, 2, 2, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0393_semantics :
    ((Generated.hostChunk032[9]).induced.toList, (Generated.hostChunk032[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[9]).mask)) := by
  have hm : (Generated.hostChunk032[9]).mask = 39523 := by decide +kernel
  have hv : ((Generated.hostChunk032[9]).induced.toList, (Generated.hostChunk032[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 2, 6, 2, 2, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0393]

theorem fixed_values_0394 :
    (fixedDensityCounts (maskGraph 7 39524), fixedComplementCounts (maskGraph 7 39524)) =
      ([0, 0, 0, 0, 0, 1, 3, 6, 2, 4, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0394_semantics :
    ((Generated.hostChunk032[10]).induced.toList, (Generated.hostChunk032[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[10]).mask)) := by
  have hm : (Generated.hostChunk032[10]).mask = 39524 := by decide +kernel
  have hv : ((Generated.hostChunk032[10]).induced.toList, (Generated.hostChunk032[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 3, 6, 2, 4, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0394]

theorem fixed_values_0395 :
    (fixedDensityCounts (maskGraph 7 39525), fixedComplementCounts (maskGraph 7 39525)) =
      ([0, 0, 0, 0, 0, 1, 2, 5, 2, 0, 4, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0395_semantics :
    ((Generated.hostChunk032[11]).induced.toList, (Generated.hostChunk032[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk032[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk032[11]).mask)) := by
  have hm : (Generated.hostChunk032[11]).mask = 39525 := by decide +kernel
  have hv : ((Generated.hostChunk032[11]).induced.toList, (Generated.hostChunk032[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 2, 5, 2, 0, 4, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0395]

theorem fixed_chunk_032_semantics :
    ∀ h ∈ Generated.hostChunk032.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk032.toList = [Generated.hostChunk032[0], Generated.hostChunk032[1], Generated.hostChunk032[2], Generated.hostChunk032[3], Generated.hostChunk032[4], Generated.hostChunk032[5], Generated.hostChunk032[6], Generated.hostChunk032[7], Generated.hostChunk032[8], Generated.hostChunk032[9], Generated.hostChunk032[10], Generated.hostChunk032[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0384_semantics
  · exact fixed_host_0385_semantics
  · exact fixed_host_0386_semantics
  · exact fixed_host_0387_semantics
  · exact fixed_host_0388_semantics
  · exact fixed_host_0389_semantics
  · exact fixed_host_0390_semantics
  · exact fixed_host_0391_semantics
  · exact fixed_host_0392_semantics
  · exact fixed_host_0393_semantics
  · exact fixed_host_0394_semantics
  · exact fixed_host_0395_semantics

end InducedPentagons.Paper

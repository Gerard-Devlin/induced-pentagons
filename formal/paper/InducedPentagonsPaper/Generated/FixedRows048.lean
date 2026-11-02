import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData048
import InducedPentagonsPaper.Generated.FixedRows040

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0576 :
    (fixedDensityCounts (maskGraph 7 44287), fixedComplementCounts (maskGraph 7 44287)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0576_semantics :
    ((Generated.hostChunk048[0]).induced.toList, (Generated.hostChunk048[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[0]).mask)) := by
  have hm : (Generated.hostChunk048[0]).mask = 44287 := by decide +kernel
  have hv : ((Generated.hostChunk048[0]).induced.toList, (Generated.hostChunk048[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0576]

theorem fixed_values_0577 :
    (fixedDensityCounts (maskGraph 7 44336), fixedComplementCounts (maskGraph 7 44336)) =
      ([0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0577_semantics :
    ((Generated.hostChunk048[1]).induced.toList, (Generated.hostChunk048[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[1]).mask)) := by
  have hm : (Generated.hostChunk048[1]).mask = 44336 := by decide +kernel
  have hv : ((Generated.hostChunk048[1]).induced.toList, (Generated.hostChunk048[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0577]

theorem fixed_values_0578 :
    (fixedDensityCounts (maskGraph 7 44337), fixedComplementCounts (maskGraph 7 44337)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 4, 0, 0, 0, 0, 8, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0578_semantics :
    ((Generated.hostChunk048[2]).induced.toList, (Generated.hostChunk048[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[2]).mask)) := by
  have hm : (Generated.hostChunk048[2]).mask = 44337 := by decide +kernel
  have hv : ((Generated.hostChunk048[2]).induced.toList, (Generated.hostChunk048[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 4, 0, 0, 0, 0, 8, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0578]

theorem fixed_values_0579 :
    (fixedDensityCounts (maskGraph 7 44339), fixedComplementCounts (maskGraph 7 44339)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0579_semantics :
    ((Generated.hostChunk048[3]).induced.toList, (Generated.hostChunk048[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[3]).mask)) := by
  have hm : (Generated.hostChunk048[3]).mask = 44339 := by decide +kernel
  have hv : ((Generated.hostChunk048[3]).induced.toList, (Generated.hostChunk048[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0579]

theorem fixed_values_0580 :
    (fixedDensityCounts (maskGraph 7 44340), fixedComplementCounts (maskGraph 7 44340)) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 4, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0580_semantics :
    ((Generated.hostChunk048[4]).induced.toList, (Generated.hostChunk048[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[4]).mask)) := by
  have hm : (Generated.hostChunk048[4]).mask = 44340 := by decide +kernel
  have hv : ((Generated.hostChunk048[4]).induced.toList, (Generated.hostChunk048[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 4, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0580]

theorem fixed_values_0581 :
    (fixedDensityCounts (maskGraph 7 44341), fixedComplementCounts (maskGraph 7 44341)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 2, 1, 0, 0, 3, 1, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0581_semantics :
    ((Generated.hostChunk048[5]).induced.toList, (Generated.hostChunk048[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[5]).mask)) := by
  have hm : (Generated.hostChunk048[5]).mask = 44341 := by decide +kernel
  have hv : ((Generated.hostChunk048[5]).induced.toList, (Generated.hostChunk048[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 2, 1, 0, 0, 3, 1, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0581]

theorem fixed_values_0582 :
    (fixedDensityCounts (maskGraph 7 44342), fixedComplementCounts (maskGraph 7 44342)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 2, 0, 0, 1, 5, 1, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0582_semantics :
    ((Generated.hostChunk048[6]).induced.toList, (Generated.hostChunk048[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[6]).mask)) := by
  have hm : (Generated.hostChunk048[6]).mask = 44342 := by decide +kernel
  have hv : ((Generated.hostChunk048[6]).induced.toList, (Generated.hostChunk048[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 2, 0, 0, 1, 5, 1, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0582]

theorem fixed_values_0583 :
    (fixedDensityCounts (maskGraph 7 44343), fixedComplementCounts (maskGraph 7 44343)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 1, 0, 0, 2, 3, 1, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0583_semantics :
    ((Generated.hostChunk048[7]).induced.toList, (Generated.hostChunk048[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[7]).mask)) := by
  have hm : (Generated.hostChunk048[7]).mask = 44343 := by decide +kernel
  have hv : ((Generated.hostChunk048[7]).induced.toList, (Generated.hostChunk048[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 1, 0, 0, 2, 3, 1, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0583]

theorem fixed_values_0584 :
    (fixedDensityCounts (maskGraph 7 44348), fixedComplementCounts (maskGraph 7 44348)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 1, 2, 0, 5, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0584_semantics :
    ((Generated.hostChunk048[8]).induced.toList, (Generated.hostChunk048[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[8]).mask)) := by
  have hm : (Generated.hostChunk048[8]).mask = 44348 := by decide +kernel
  have hv : ((Generated.hostChunk048[8]).induced.toList, (Generated.hostChunk048[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 1, 2, 0, 5, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0584]

theorem fixed_values_0585 :
    (fixedDensityCounts (maskGraph 7 44349), fixedComplementCounts (maskGraph 7 44349)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 2, 0, 1, 2, 1, 2, 2, 0, 0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0585_semantics :
    ((Generated.hostChunk048[9]).induced.toList, (Generated.hostChunk048[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[9]).mask)) := by
  have hm : (Generated.hostChunk048[9]).mask = 44349 := by decide +kernel
  have hv : ((Generated.hostChunk048[9]).induced.toList, (Generated.hostChunk048[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 2, 0, 1, 2, 1, 2, 2, 0, 0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0585]

theorem fixed_values_0586 :
    (fixedDensityCounts (maskGraph 7 44351), fixedComplementCounts (maskGraph 7 44351)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 3, 0, 0, 2, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0586_semantics :
    ((Generated.hostChunk048[10]).induced.toList, (Generated.hostChunk048[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[10]).mask)) := by
  have hm : (Generated.hostChunk048[10]).mask = 44351 := by decide +kernel
  have hv : ((Generated.hostChunk048[10]).induced.toList, (Generated.hostChunk048[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 3, 0, 0, 2, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0586]

theorem fixed_values_0587 :
    (fixedDensityCounts (maskGraph 7 44403), fixedComplementCounts (maskGraph 7 44403)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0587_semantics :
    ((Generated.hostChunk048[11]).induced.toList, (Generated.hostChunk048[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk048[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk048[11]).mask)) := by
  have hm : (Generated.hostChunk048[11]).mask = 44403 := by decide +kernel
  have hv : ((Generated.hostChunk048[11]).induced.toList, (Generated.hostChunk048[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0587]

theorem fixed_chunk_048_semantics :
    ∀ h ∈ Generated.hostChunk048.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk048.toList = [Generated.hostChunk048[0], Generated.hostChunk048[1], Generated.hostChunk048[2], Generated.hostChunk048[3], Generated.hostChunk048[4], Generated.hostChunk048[5], Generated.hostChunk048[6], Generated.hostChunk048[7], Generated.hostChunk048[8], Generated.hostChunk048[9], Generated.hostChunk048[10], Generated.hostChunk048[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0576_semantics
  · exact fixed_host_0577_semantics
  · exact fixed_host_0578_semantics
  · exact fixed_host_0579_semantics
  · exact fixed_host_0580_semantics
  · exact fixed_host_0581_semantics
  · exact fixed_host_0582_semantics
  · exact fixed_host_0583_semantics
  · exact fixed_host_0584_semantics
  · exact fixed_host_0585_semantics
  · exact fixed_host_0586_semantics
  · exact fixed_host_0587_semantics

end InducedPentagons.Paper

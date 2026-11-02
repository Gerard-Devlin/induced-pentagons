import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData046
import InducedPentagonsPaper.Generated.FixedRows038

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0552 :
    (fixedDensityCounts (maskGraph 7 43900), fixedComplementCounts (maskGraph 7 43900)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0552_semantics :
    ((Generated.hostChunk046[0]).induced.toList, (Generated.hostChunk046[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[0]).mask)) := by
  have hm : (Generated.hostChunk046[0]).mask = 43900 := by decide +kernel
  have hv : ((Generated.hostChunk046[0]).induced.toList, (Generated.hostChunk046[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0552]

theorem fixed_values_0553 :
    (fixedDensityCounts (maskGraph 7 43901), fixedComplementCounts (maskGraph 7 43901)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 2, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0553_semantics :
    ((Generated.hostChunk046[1]).induced.toList, (Generated.hostChunk046[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[1]).mask)) := by
  have hm : (Generated.hostChunk046[1]).mask = 43901 := by decide +kernel
  have hv : ((Generated.hostChunk046[1]).induced.toList, (Generated.hostChunk046[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 2, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0553]

theorem fixed_values_0554 :
    (fixedDensityCounts (maskGraph 7 43903), fixedComplementCounts (maskGraph 7 43903)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0554_semantics :
    ((Generated.hostChunk046[2]).induced.toList, (Generated.hostChunk046[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[2]).mask)) := by
  have hm : (Generated.hostChunk046[2]).mask = 43903 := by decide +kernel
  have hv : ((Generated.hostChunk046[2]).induced.toList, (Generated.hostChunk046[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0554]

theorem fixed_values_0555 :
    (fixedDensityCounts (maskGraph 7 43998), fixedComplementCounts (maskGraph 7 43998)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 3, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0555_semantics :
    ((Generated.hostChunk046[3]).induced.toList, (Generated.hostChunk046[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[3]).mask)) := by
  have hm : (Generated.hostChunk046[3]).mask = 43998 := by decide +kernel
  have hv : ((Generated.hostChunk046[3]).induced.toList, (Generated.hostChunk046[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 3, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0555]

theorem fixed_values_0556 :
    (fixedDensityCounts (maskGraph 7 43999), fixedComplementCounts (maskGraph 7 43999)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0556_semantics :
    ((Generated.hostChunk046[4]).induced.toList, (Generated.hostChunk046[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[4]).mask)) := by
  have hm : (Generated.hostChunk046[4]).mask = 43999 := by decide +kernel
  have hv : ((Generated.hostChunk046[4]).induced.toList, (Generated.hostChunk046[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0556]

theorem fixed_values_0557 :
    (fixedDensityCounts (maskGraph 7 44006), fixedComplementCounts (maskGraph 7 44006)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 2, 2, 5, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0557_semantics :
    ((Generated.hostChunk046[5]).induced.toList, (Generated.hostChunk046[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[5]).mask)) := by
  have hm : (Generated.hostChunk046[5]).mask = 44006 := by decide +kernel
  have hv : ((Generated.hostChunk046[5]).induced.toList, (Generated.hostChunk046[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 2, 2, 5, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0557]

theorem fixed_values_0558 :
    (fixedDensityCounts (maskGraph 7 44007), fixedComplementCounts (maskGraph 7 44007)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 1, 0, 0, 2, 0, 5, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0558_semantics :
    ((Generated.hostChunk046[6]).induced.toList, (Generated.hostChunk046[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[6]).mask)) := by
  have hm : (Generated.hostChunk046[6]).mask = 44007 := by decide +kernel
  have hv : ((Generated.hostChunk046[6]).induced.toList, (Generated.hostChunk046[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 1, 0, 0, 2, 0, 5, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0558]

theorem fixed_values_0559 :
    (fixedDensityCounts (maskGraph 7 44008), fixedComplementCounts (maskGraph 7 44008)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 3, 4, 1, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0559_semantics :
    ((Generated.hostChunk046[7]).induced.toList, (Generated.hostChunk046[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[7]).mask)) := by
  have hm : (Generated.hostChunk046[7]).mask = 44008 := by decide +kernel
  have hv : ((Generated.hostChunk046[7]).induced.toList, (Generated.hostChunk046[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 3, 4, 1, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0559]

theorem fixed_values_0560 :
    (fixedDensityCounts (maskGraph 7 44009), fixedComplementCounts (maskGraph 7 44009)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0560_semantics :
    ((Generated.hostChunk046[8]).induced.toList, (Generated.hostChunk046[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[8]).mask)) := by
  have hm : (Generated.hostChunk046[8]).mask = 44009 := by decide +kernel
  have hv : ((Generated.hostChunk046[8]).induced.toList, (Generated.hostChunk046[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0560]

theorem fixed_values_0561 :
    (fixedDensityCounts (maskGraph 7 44010), fixedComplementCounts (maskGraph 7 44010)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 0, 0, 2, 1, 1, 3, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0561_semantics :
    ((Generated.hostChunk046[9]).induced.toList, (Generated.hostChunk046[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[9]).mask)) := by
  have hm : (Generated.hostChunk046[9]).mask = 44010 := by decide +kernel
  have hv : ((Generated.hostChunk046[9]).induced.toList, (Generated.hostChunk046[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 0, 0, 2, 1, 1, 3, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0561]

theorem fixed_values_0562 :
    (fixedDensityCounts (maskGraph 7 44011), fixedComplementCounts (maskGraph 7 44011)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 3, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0562_semantics :
    ((Generated.hostChunk046[10]).induced.toList, (Generated.hostChunk046[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[10]).mask)) := by
  have hm : (Generated.hostChunk046[10]).mask = 44011 := by decide +kernel
  have hv : ((Generated.hostChunk046[10]).induced.toList, (Generated.hostChunk046[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 3, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0562]

theorem fixed_values_0563 :
    (fixedDensityCounts (maskGraph 7 44012), fixedComplementCounts (maskGraph 7 44012)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0563_semantics :
    ((Generated.hostChunk046[11]).induced.toList, (Generated.hostChunk046[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk046[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk046[11]).mask)) := by
  have hm : (Generated.hostChunk046[11]).mask = 44012 := by decide +kernel
  have hv : ((Generated.hostChunk046[11]).induced.toList, (Generated.hostChunk046[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0563]

theorem fixed_chunk_046_semantics :
    ∀ h ∈ Generated.hostChunk046.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk046.toList = [Generated.hostChunk046[0], Generated.hostChunk046[1], Generated.hostChunk046[2], Generated.hostChunk046[3], Generated.hostChunk046[4], Generated.hostChunk046[5], Generated.hostChunk046[6], Generated.hostChunk046[7], Generated.hostChunk046[8], Generated.hostChunk046[9], Generated.hostChunk046[10], Generated.hostChunk046[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0552_semantics
  · exact fixed_host_0553_semantics
  · exact fixed_host_0554_semantics
  · exact fixed_host_0555_semantics
  · exact fixed_host_0556_semantics
  · exact fixed_host_0557_semantics
  · exact fixed_host_0558_semantics
  · exact fixed_host_0559_semantics
  · exact fixed_host_0560_semantics
  · exact fixed_host_0561_semantics
  · exact fixed_host_0562_semantics
  · exact fixed_host_0563_semantics

end InducedPentagons.Paper

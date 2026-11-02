import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData016
import InducedPentagonsPaper.Generated.FixedRows008

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0192 :
    (fixedDensityCounts (maskGraph 7 6559), fixedComplementCounts (maskGraph 7 6559)) =
      ([0, 0, 4, 2, 0, 0, 0, 0, 4, 0, 0, 0, 2, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0192_semantics :
    ((Generated.hostChunk016[0]).induced.toList, (Generated.hostChunk016[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[0]).mask)) := by
  have hm : (Generated.hostChunk016[0]).mask = 6559 := by decide +kernel
  have hv : ((Generated.hostChunk016[0]).induced.toList, (Generated.hostChunk016[0]).complement.toList) =
      ([0, 0, 4, 2, 0, 0, 0, 0, 4, 0, 0, 0, 2, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0192]

theorem fixed_values_0193 :
    (fixedDensityCounts (maskGraph 7 6576), fixedComplementCounts (maskGraph 7 6576)) =
      ([0, 0, 6, 0, 0, 0, 0, 0, 0, 12, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0193_semantics :
    ((Generated.hostChunk016[1]).induced.toList, (Generated.hostChunk016[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[1]).mask)) := by
  have hm : (Generated.hostChunk016[1]).mask = 6576 := by decide +kernel
  have hv : ((Generated.hostChunk016[1]).induced.toList, (Generated.hostChunk016[1]).complement.toList) =
      ([0, 0, 6, 0, 0, 0, 0, 0, 0, 12, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0193]

theorem fixed_values_0194 :
    (fixedDensityCounts (maskGraph 7 6577), fixedComplementCounts (maskGraph 7 6577)) =
      ([0, 0, 5, 1, 0, 0, 0, 0, 0, 4, 4, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0194_semantics :
    ((Generated.hostChunk016[2]).induced.toList, (Generated.hostChunk016[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[2]).mask)) := by
  have hm : (Generated.hostChunk016[2]).mask = 6577 := by decide +kernel
  have hv : ((Generated.hostChunk016[2]).induced.toList, (Generated.hostChunk016[2]).complement.toList) =
      ([0, 0, 5, 1, 0, 0, 0, 0, 0, 4, 4, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0194]

theorem fixed_values_0195 :
    (fixedDensityCounts (maskGraph 7 6579), fixedComplementCounts (maskGraph 7 6579)) =
      ([0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 8, 0, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0195_semantics :
    ((Generated.hostChunk016[3]).induced.toList, (Generated.hostChunk016[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[3]).mask)) := by
  have hm : (Generated.hostChunk016[3]).mask = 6579 := by decide +kernel
  have hv : ((Generated.hostChunk016[3]).induced.toList, (Generated.hostChunk016[3]).complement.toList) =
      ([0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 8, 0, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0195]

theorem fixed_values_0196 :
    (fixedDensityCounts (maskGraph 7 6581), fixedComplementCounts (maskGraph 7 6581)) =
      ([0, 0, 4, 2, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0196_semantics :
    ((Generated.hostChunk016[4]).induced.toList, (Generated.hostChunk016[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[4]).mask)) := by
  have hm : (Generated.hostChunk016[4]).mask = 6581 := by decide +kernel
  have hv : ((Generated.hostChunk016[4]).induced.toList, (Generated.hostChunk016[4]).complement.toList) =
      ([0, 0, 4, 2, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0196]

theorem fixed_values_0197 :
    (fixedDensityCounts (maskGraph 7 6583), fixedComplementCounts (maskGraph 7 6583)) =
      ([0, 0, 4, 1, 1, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0197_semantics :
    ((Generated.hostChunk016[5]).induced.toList, (Generated.hostChunk016[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[5]).mask)) := by
  have hm : (Generated.hostChunk016[5]).mask = 6583 := by decide +kernel
  have hv : ((Generated.hostChunk016[5]).induced.toList, (Generated.hostChunk016[5]).complement.toList) =
      ([0, 0, 4, 1, 1, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 4, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0197]

theorem fixed_values_0198 :
    (fixedDensityCounts (maskGraph 7 6591), fixedComplementCounts (maskGraph 7 6591)) =
      ([0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0198_semantics :
    ((Generated.hostChunk016[6]).induced.toList, (Generated.hostChunk016[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[6]).mask)) := by
  have hm : (Generated.hostChunk016[6]).mask = 6591 := by decide +kernel
  have hv : ((Generated.hostChunk016[6]).induced.toList, (Generated.hostChunk016[6]).complement.toList) =
      ([0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0198]

theorem fixed_values_0199 :
    (fixedDensityCounts (maskGraph 7 6607), fixedComplementCounts (maskGraph 7 6607)) =
      ([0, 0, 3, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 3, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0199_semantics :
    ((Generated.hostChunk016[7]).induced.toList, (Generated.hostChunk016[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[7]).mask)) := by
  have hm : (Generated.hostChunk016[7]).mask = 6607 := by decide +kernel
  have hv : ((Generated.hostChunk016[7]).induced.toList, (Generated.hostChunk016[7]).complement.toList) =
      ([0, 0, 3, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 3, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0199]

theorem fixed_values_0200 :
    (fixedDensityCounts (maskGraph 7 6612), fixedComplementCounts (maskGraph 7 6612)) =
      ([0, 0, 3, 0, 0, 3, 3, 4, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0200_semantics :
    ((Generated.hostChunk016[8]).induced.toList, (Generated.hostChunk016[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[8]).mask)) := by
  have hm : (Generated.hostChunk016[8]).mask = 6612 := by decide +kernel
  have hv : ((Generated.hostChunk016[8]).induced.toList, (Generated.hostChunk016[8]).complement.toList) =
      ([0, 0, 3, 0, 0, 3, 3, 4, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0200]

theorem fixed_values_0201 :
    (fixedDensityCounts (maskGraph 7 6613), fixedComplementCounts (maskGraph 7 6613)) =
      ([0, 0, 3, 0, 0, 2, 1, 4, 3, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0201_semantics :
    ((Generated.hostChunk016[9]).induced.toList, (Generated.hostChunk016[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[9]).mask)) := by
  have hm : (Generated.hostChunk016[9]).mask = 6613 := by decide +kernel
  have hv : ((Generated.hostChunk016[9]).induced.toList, (Generated.hostChunk016[9]).complement.toList) =
      ([0, 0, 3, 0, 0, 2, 1, 4, 3, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0201]

theorem fixed_values_0202 :
    (fixedDensityCounts (maskGraph 7 6615), fixedComplementCounts (maskGraph 7 6615)) =
      ([0, 0, 3, 0, 0, 2, 0, 2, 5, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0202_semantics :
    ((Generated.hostChunk016[10]).induced.toList, (Generated.hostChunk016[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[10]).mask)) := by
  have hm : (Generated.hostChunk016[10]).mask = 6615 := by decide +kernel
  have hv : ((Generated.hostChunk016[10]).induced.toList, (Generated.hostChunk016[10]).complement.toList) =
      ([0, 0, 3, 0, 0, 2, 0, 2, 5, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0202]

theorem fixed_values_0203 :
    (fixedDensityCounts (maskGraph 7 6620), fixedComplementCounts (maskGraph 7 6620)) =
      ([0, 0, 2, 1, 0, 2, 1, 4, 2, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0203_semantics :
    ((Generated.hostChunk016[11]).induced.toList, (Generated.hostChunk016[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk016[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk016[11]).mask)) := by
  have hm : (Generated.hostChunk016[11]).mask = 6620 := by decide +kernel
  have hv : ((Generated.hostChunk016[11]).induced.toList, (Generated.hostChunk016[11]).complement.toList) =
      ([0, 0, 2, 1, 0, 2, 1, 4, 2, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0203]

theorem fixed_chunk_016_semantics :
    ∀ h ∈ Generated.hostChunk016.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk016.toList = [Generated.hostChunk016[0], Generated.hostChunk016[1], Generated.hostChunk016[2], Generated.hostChunk016[3], Generated.hostChunk016[4], Generated.hostChunk016[5], Generated.hostChunk016[6], Generated.hostChunk016[7], Generated.hostChunk016[8], Generated.hostChunk016[9], Generated.hostChunk016[10], Generated.hostChunk016[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0192_semantics
  · exact fixed_host_0193_semantics
  · exact fixed_host_0194_semantics
  · exact fixed_host_0195_semantics
  · exact fixed_host_0196_semantics
  · exact fixed_host_0197_semantics
  · exact fixed_host_0198_semantics
  · exact fixed_host_0199_semantics
  · exact fixed_host_0200_semantics
  · exact fixed_host_0201_semantics
  · exact fixed_host_0202_semantics
  · exact fixed_host_0203_semantics

end InducedPentagons.Paper

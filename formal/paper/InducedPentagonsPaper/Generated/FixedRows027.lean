import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData027
import InducedPentagonsPaper.Generated.FixedRows019

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0324 :
    (fixedDensityCounts (maskGraph 7 15261), fixedComplementCounts (maskGraph 7 15261)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 6, 3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0324_semantics :
    ((Generated.hostChunk027[0]).induced.toList, (Generated.hostChunk027[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[0]).mask)) := by
  have hm : (Generated.hostChunk027[0]).mask = 15261 := by decide +kernel
  have hv : ((Generated.hostChunk027[0]).induced.toList, (Generated.hostChunk027[0]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 6, 3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0324]

theorem fixed_values_0325 :
    (fixedDensityCounts (maskGraph 7 15263), fixedComplementCounts (maskGraph 7 15263)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 9, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0325_semantics :
    ((Generated.hostChunk027[1]).induced.toList, (Generated.hostChunk027[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[1]).mask)) := by
  have hm : (Generated.hostChunk027[1]).mask = 15263 := by decide +kernel
  have hv : ((Generated.hostChunk027[1]).induced.toList, (Generated.hostChunk027[1]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 9, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0325]

theorem fixed_values_0326 :
    (fixedDensityCounts (maskGraph 7 15276), fixedComplementCounts (maskGraph 7 15276)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 4, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0326_semantics :
    ((Generated.hostChunk027[2]).induced.toList, (Generated.hostChunk027[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[2]).mask)) := by
  have hm : (Generated.hostChunk027[2]).mask = 15276 := by decide +kernel
  have hv : ((Generated.hostChunk027[2]).induced.toList, (Generated.hostChunk027[2]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 4, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0326]

theorem fixed_values_0327 :
    (fixedDensityCounts (maskGraph 7 15277), fixedComplementCounts (maskGraph 7 15277)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 4, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0327_semantics :
    ((Generated.hostChunk027[3]).induced.toList, (Generated.hostChunk027[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[3]).mask)) := by
  have hm : (Generated.hostChunk027[3]).mask = 15277 := by decide +kernel
  have hv : ((Generated.hostChunk027[3]).induced.toList, (Generated.hostChunk027[3]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 4, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0327]

theorem fixed_values_0328 :
    (fixedDensityCounts (maskGraph 7 15279), fixedComplementCounts (maskGraph 7 15279)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 1, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0328_semantics :
    ((Generated.hostChunk027[4]).induced.toList, (Generated.hostChunk027[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[4]).mask)) := by
  have hm : (Generated.hostChunk027[4]).mask = 15279 := by decide +kernel
  have hv : ((Generated.hostChunk027[4]).induced.toList, (Generated.hostChunk027[4]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 1, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0328]

theorem fixed_values_0329 :
    (fixedDensityCounts (maskGraph 7 15292), fixedComplementCounts (maskGraph 7 15292)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0329_semantics :
    ((Generated.hostChunk027[5]).induced.toList, (Generated.hostChunk027[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[5]).mask)) := by
  have hm : (Generated.hostChunk027[5]).mask = 15292 := by decide +kernel
  have hv : ((Generated.hostChunk027[5]).induced.toList, (Generated.hostChunk027[5]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0329]

theorem fixed_values_0330 :
    (fixedDensityCounts (maskGraph 7 15293), fixedComplementCounts (maskGraph 7 15293)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0330_semantics :
    ((Generated.hostChunk027[6]).induced.toList, (Generated.hostChunk027[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[6]).mask)) := by
  have hm : (Generated.hostChunk027[6]).mask = 15293 := by decide +kernel
  have hv : ((Generated.hostChunk027[6]).induced.toList, (Generated.hostChunk027[6]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0330]

theorem fixed_values_0331 :
    (fixedDensityCounts (maskGraph 7 15295), fixedComplementCounts (maskGraph 7 15295)) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 9, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0331_semantics :
    ((Generated.hostChunk027[7]).induced.toList, (Generated.hostChunk027[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[7]).mask)) := by
  have hm : (Generated.hostChunk027[7]).mask = 15295 := by decide +kernel
  have hv : ((Generated.hostChunk027[7]).induced.toList, (Generated.hostChunk027[7]).complement.toList) =
      ([0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 9, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0331]

theorem fixed_values_0332 :
    (fixedDensityCounts (maskGraph 7 15327), fixedComplementCounts (maskGraph 7 15327)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0332_semantics :
    ((Generated.hostChunk027[8]).induced.toList, (Generated.hostChunk027[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[8]).mask)) := by
  have hm : (Generated.hostChunk027[8]).mask = 15327 := by decide +kernel
  have hv : ((Generated.hostChunk027[8]).induced.toList, (Generated.hostChunk027[8]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0332]

theorem fixed_values_0333 :
    (fixedDensityCounts (maskGraph 7 15340), fixedComplementCounts (maskGraph 7 15340)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 4, 0, 0, 1, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0333_semantics :
    ((Generated.hostChunk027[9]).induced.toList, (Generated.hostChunk027[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[9]).mask)) := by
  have hm : (Generated.hostChunk027[9]).mask = 15340 := by decide +kernel
  have hv : ((Generated.hostChunk027[9]).induced.toList, (Generated.hostChunk027[9]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 4, 0, 0, 1, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0333]

theorem fixed_values_0334 :
    (fixedDensityCounts (maskGraph 7 15341), fixedComplementCounts (maskGraph 7 15341)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 2, 2, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0334_semantics :
    ((Generated.hostChunk027[10]).induced.toList, (Generated.hostChunk027[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[10]).mask)) := by
  have hm : (Generated.hostChunk027[10]).mask = 15341 := by decide +kernel
  have hv : ((Generated.hostChunk027[10]).induced.toList, (Generated.hostChunk027[10]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 2, 2, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0334]

theorem fixed_values_0335 :
    (fixedDensityCounts (maskGraph 7 15343), fixedComplementCounts (maskGraph 7 15343)) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 4, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0335_semantics :
    ((Generated.hostChunk027[11]).induced.toList, (Generated.hostChunk027[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk027[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk027[11]).mask)) := by
  have hm : (Generated.hostChunk027[11]).mask = 15343 := by decide +kernel
  have hv : ((Generated.hostChunk027[11]).induced.toList, (Generated.hostChunk027[11]).complement.toList) =
      ([0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 4, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0335]

theorem fixed_chunk_027_semantics :
    ∀ h ∈ Generated.hostChunk027.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk027.toList = [Generated.hostChunk027[0], Generated.hostChunk027[1], Generated.hostChunk027[2], Generated.hostChunk027[3], Generated.hostChunk027[4], Generated.hostChunk027[5], Generated.hostChunk027[6], Generated.hostChunk027[7], Generated.hostChunk027[8], Generated.hostChunk027[9], Generated.hostChunk027[10], Generated.hostChunk027[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0324_semantics
  · exact fixed_host_0325_semantics
  · exact fixed_host_0326_semantics
  · exact fixed_host_0327_semantics
  · exact fixed_host_0328_semantics
  · exact fixed_host_0329_semantics
  · exact fixed_host_0330_semantics
  · exact fixed_host_0331_semantics
  · exact fixed_host_0332_semantics
  · exact fixed_host_0333_semantics
  · exact fixed_host_0334_semantics
  · exact fixed_host_0335_semantics

end InducedPentagons.Paper

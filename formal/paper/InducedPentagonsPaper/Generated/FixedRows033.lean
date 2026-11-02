import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData033
import InducedPentagonsPaper.Generated.FixedRows025

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0396 :
    (fixedDensityCounts (maskGraph 7 39526), fixedComplementCounts (maskGraph 7 39526)) =
      ([0, 0, 0, 0, 0, 1, 2, 5, 2, 2, 2, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0396_semantics :
    ((Generated.hostChunk033[0]).induced.toList, (Generated.hostChunk033[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[0]).mask)) := by
  have hm : (Generated.hostChunk033[0]).mask = 39526 := by decide +kernel
  have hv : ((Generated.hostChunk033[0]).induced.toList, (Generated.hostChunk033[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 2, 5, 2, 2, 2, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0396]

theorem fixed_values_0397 :
    (fixedDensityCounts (maskGraph 7 39527), fixedComplementCounts (maskGraph 7 39527)) =
      ([0, 0, 0, 0, 0, 1, 1, 5, 2, 0, 2, 0, 0, 1, 1, 3, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 3, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0397_semantics :
    ((Generated.hostChunk033[1]).induced.toList, (Generated.hostChunk033[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[1]).mask)) := by
  have hm : (Generated.hostChunk033[1]).mask = 39527 := by decide +kernel
  have hv : ((Generated.hostChunk033[1]).induced.toList, (Generated.hostChunk033[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 5, 2, 0, 2, 0, 0, 1, 1, 3, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 3, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0397]

theorem fixed_values_0398 :
    (fixedDensityCounts (maskGraph 7 39532), fixedComplementCounts (maskGraph 7 39532)) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 3, 3, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0398_semantics :
    ((Generated.hostChunk033[2]).induced.toList, (Generated.hostChunk033[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[2]).mask)) := by
  have hm : (Generated.hostChunk033[2]).mask = 39532 := by decide +kernel
  have hv : ((Generated.hostChunk033[2]).induced.toList, (Generated.hostChunk033[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 3, 3, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0398]

theorem fixed_values_0399 :
    (fixedDensityCounts (maskGraph 7 39533), fixedComplementCounts (maskGraph 7 39533)) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 2, 0, 3, 1, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0399_semantics :
    ((Generated.hostChunk033[3]).induced.toList, (Generated.hostChunk033[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[3]).mask)) := by
  have hm : (Generated.hostChunk033[3]).mask = 39533 := by decide +kernel
  have hv : ((Generated.hostChunk033[3]).induced.toList, (Generated.hostChunk033[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 2, 0, 3, 1, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0399]

theorem fixed_values_0400 :
    (fixedDensityCounts (maskGraph 7 39534), fixedComplementCounts (maskGraph 7 39534)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 5, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0400_semantics :
    ((Generated.hostChunk033[4]).induced.toList, (Generated.hostChunk033[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[4]).mask)) := by
  have hm : (Generated.hostChunk033[4]).mask = 39534 := by decide +kernel
  have hv : ((Generated.hostChunk033[4]).induced.toList, (Generated.hostChunk033[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 5, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0400]

theorem fixed_values_0401 :
    (fixedDensityCounts (maskGraph 7 39535), fixedComplementCounts (maskGraph 7 39535)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0401_semantics :
    ((Generated.hostChunk033[5]).induced.toList, (Generated.hostChunk033[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[5]).mask)) := by
  have hm : (Generated.hostChunk033[5]).mask = 39535 := by decide +kernel
  have hv : ((Generated.hostChunk033[5]).induced.toList, (Generated.hostChunk033[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0401]

theorem fixed_values_0402 :
    (fixedDensityCounts (maskGraph 7 39536), fixedComplementCounts (maskGraph 7 39536)) =
      ([0, 0, 0, 0, 0, 1, 2, 4, 2, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0402_semantics :
    ((Generated.hostChunk033[6]).induced.toList, (Generated.hostChunk033[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[6]).mask)) := by
  have hm : (Generated.hostChunk033[6]).mask = 39536 := by decide +kernel
  have hv : ((Generated.hostChunk033[6]).induced.toList, (Generated.hostChunk033[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 2, 4, 2, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0402]

theorem fixed_values_0403 :
    (fixedDensityCounts (maskGraph 7 39537), fixedComplementCounts (maskGraph 7 39537)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0403_semantics :
    ((Generated.hostChunk033[7]).induced.toList, (Generated.hostChunk033[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[7]).mask)) := by
  have hm : (Generated.hostChunk033[7]).mask = 39537 := by decide +kernel
  have hv : ((Generated.hostChunk033[7]).induced.toList, (Generated.hostChunk033[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0403]

theorem fixed_values_0404 :
    (fixedDensityCounts (maskGraph 7 39538), fixedComplementCounts (maskGraph 7 39538)) =
      ([0, 0, 0, 0, 0, 1, 2, 4, 1, 2, 4, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0404_semantics :
    ((Generated.hostChunk033[8]).induced.toList, (Generated.hostChunk033[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[8]).mask)) := by
  have hm : (Generated.hostChunk033[8]).mask = 39538 := by decide +kernel
  have hv : ((Generated.hostChunk033[8]).induced.toList, (Generated.hostChunk033[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 2, 4, 1, 2, 4, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0404]

theorem fixed_values_0405 :
    (fixedDensityCounts (maskGraph 7 39539), fixedComplementCounts (maskGraph 7 39539)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0405_semantics :
    ((Generated.hostChunk033[9]).induced.toList, (Generated.hostChunk033[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[9]).mask)) := by
  have hm : (Generated.hostChunk033[9]).mask = 39539 := by decide +kernel
  have hv : ((Generated.hostChunk033[9]).induced.toList, (Generated.hostChunk033[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0405]

theorem fixed_values_0406 :
    (fixedDensityCounts (maskGraph 7 39540), fixedComplementCounts (maskGraph 7 39540)) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 1, 2, 3, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0406_semantics :
    ((Generated.hostChunk033[10]).induced.toList, (Generated.hostChunk033[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[10]).mask)) := by
  have hm : (Generated.hostChunk033[10]).mask = 39540 := by decide +kernel
  have hv : ((Generated.hostChunk033[10]).induced.toList, (Generated.hostChunk033[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 4, 1, 2, 3, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0406]

theorem fixed_values_0407 :
    (fixedDensityCounts (maskGraph 7 39541), fixedComplementCounts (maskGraph 7 39541)) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 3, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0407_semantics :
    ((Generated.hostChunk033[11]).induced.toList, (Generated.hostChunk033[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk033[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk033[11]).mask)) := by
  have hm : (Generated.hostChunk033[11]).mask = 39541 := by decide +kernel
  have hv : ((Generated.hostChunk033[11]).induced.toList, (Generated.hostChunk033[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 3, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0407]

theorem fixed_chunk_033_semantics :
    ∀ h ∈ Generated.hostChunk033.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk033.toList = [Generated.hostChunk033[0], Generated.hostChunk033[1], Generated.hostChunk033[2], Generated.hostChunk033[3], Generated.hostChunk033[4], Generated.hostChunk033[5], Generated.hostChunk033[6], Generated.hostChunk033[7], Generated.hostChunk033[8], Generated.hostChunk033[9], Generated.hostChunk033[10], Generated.hostChunk033[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0396_semantics
  · exact fixed_host_0397_semantics
  · exact fixed_host_0398_semantics
  · exact fixed_host_0399_semantics
  · exact fixed_host_0400_semantics
  · exact fixed_host_0401_semantics
  · exact fixed_host_0402_semantics
  · exact fixed_host_0403_semantics
  · exact fixed_host_0404_semantics
  · exact fixed_host_0405_semantics
  · exact fixed_host_0406_semantics
  · exact fixed_host_0407_semantics

end InducedPentagons.Paper

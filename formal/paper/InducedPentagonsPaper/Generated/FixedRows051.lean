import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData051
import InducedPentagonsPaper.Generated.FixedRows043

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0612 :
    (fixedDensityCounts (maskGraph 7 44527), fixedComplementCounts (maskGraph 7 44527)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0612_semantics :
    ((Generated.hostChunk051[0]).induced.toList, (Generated.hostChunk051[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[0]).mask)) := by
  have hm : (Generated.hostChunk051[0]).mask = 44527 := by decide +kernel
  have hv : ((Generated.hostChunk051[0]).induced.toList, (Generated.hostChunk051[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0612]

theorem fixed_values_0613 :
    (fixedDensityCounts (maskGraph 7 44534), fixedComplementCounts (maskGraph 7 44534)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0613_semantics :
    ((Generated.hostChunk051[1]).induced.toList, (Generated.hostChunk051[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[1]).mask)) := by
  have hm : (Generated.hostChunk051[1]).mask = 44534 := by decide +kernel
  have hv : ((Generated.hostChunk051[1]).induced.toList, (Generated.hostChunk051[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0613]

theorem fixed_values_0614 :
    (fixedDensityCounts (maskGraph 7 44535), fixedComplementCounts (maskGraph 7 44535)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0614_semantics :
    ((Generated.hostChunk051[2]).induced.toList, (Generated.hostChunk051[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[2]).mask)) := by
  have hm : (Generated.hostChunk051[2]).mask = 44535 := by decide +kernel
  have hv : ((Generated.hostChunk051[2]).induced.toList, (Generated.hostChunk051[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0614]

theorem fixed_values_0615 :
    (fixedDensityCounts (maskGraph 7 44536), fixedComplementCounts (maskGraph 7 44536)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0, 0, 3, 1, 2, 1, 0, 0, 0, 0, 3, 2, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0615_semantics :
    ((Generated.hostChunk051[3]).induced.toList, (Generated.hostChunk051[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[3]).mask)) := by
  have hm : (Generated.hostChunk051[3]).mask = 44536 := by decide +kernel
  have hv : ((Generated.hostChunk051[3]).induced.toList, (Generated.hostChunk051[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0, 0, 3, 1, 2, 1, 0, 0, 0, 0, 3, 2, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0615]

theorem fixed_values_0616 :
    (fixedDensityCounts (maskGraph 7 44537), fixedComplementCounts (maskGraph 7 44537)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0, 0, 2, 2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 1, 3, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0616_semantics :
    ((Generated.hostChunk051[4]).induced.toList, (Generated.hostChunk051[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[4]).mask)) := by
  have hm : (Generated.hostChunk051[4]).mask = 44537 := by decide +kernel
  have hv : ((Generated.hostChunk051[4]).induced.toList, (Generated.hostChunk051[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0, 0, 2, 2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 1, 3, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0616]

theorem fixed_values_0617 :
    (fixedDensityCounts (maskGraph 7 44538), fixedComplementCounts (maskGraph 7 44538)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 1, 2, 2, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 5, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0617_semantics :
    ((Generated.hostChunk051[5]).induced.toList, (Generated.hostChunk051[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[5]).mask)) := by
  have hm : (Generated.hostChunk051[5]).mask = 44538 := by decide +kernel
  have hv : ((Generated.hostChunk051[5]).induced.toList, (Generated.hostChunk051[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 1, 2, 2, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 5, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0617]

theorem fixed_values_0618 :
    (fixedDensityCounts (maskGraph 7 44539), fixedComplementCounts (maskGraph 7 44539)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 3, 1, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 5, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0618_semantics :
    ((Generated.hostChunk051[6]).induced.toList, (Generated.hostChunk051[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[6]).mask)) := by
  have hm : (Generated.hostChunk051[6]).mask = 44539 := by decide +kernel
  have hv : ((Generated.hostChunk051[6]).induced.toList, (Generated.hostChunk051[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 3, 1, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 5, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0618]

theorem fixed_values_0619 :
    (fixedDensityCounts (maskGraph 7 44540), fixedComplementCounts (maskGraph 7 44540)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0619_semantics :
    ((Generated.hostChunk051[7]).induced.toList, (Generated.hostChunk051[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[7]).mask)) := by
  have hm : (Generated.hostChunk051[7]).mask = 44540 := by decide +kernel
  have hv : ((Generated.hostChunk051[7]).induced.toList, (Generated.hostChunk051[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0619]

theorem fixed_values_0620 :
    (fixedDensityCounts (maskGraph 7 44541), fixedComplementCounts (maskGraph 7 44541)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0620_semantics :
    ((Generated.hostChunk051[8]).induced.toList, (Generated.hostChunk051[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[8]).mask)) := by
  have hm : (Generated.hostChunk051[8]).mask = 44541 := by decide +kernel
  have hv : ((Generated.hostChunk051[8]).induced.toList, (Generated.hostChunk051[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0620]

theorem fixed_values_0621 :
    (fixedDensityCounts (maskGraph 7 44542), fixedComplementCounts (maskGraph 7 44542)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 1, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0621_semantics :
    ((Generated.hostChunk051[9]).induced.toList, (Generated.hostChunk051[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[9]).mask)) := by
  have hm : (Generated.hostChunk051[9]).mask = 44542 := by decide +kernel
  have hv : ((Generated.hostChunk051[9]).induced.toList, (Generated.hostChunk051[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 1, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0621]

theorem fixed_values_0622 :
    (fixedDensityCounts (maskGraph 7 44543), fixedComplementCounts (maskGraph 7 44543)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 1, 0, 5, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 3, 0, 3, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0622_semantics :
    ((Generated.hostChunk051[10]).induced.toList, (Generated.hostChunk051[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[10]).mask)) := by
  have hm : (Generated.hostChunk051[10]).mask = 44543 := by decide +kernel
  have hv : ((Generated.hostChunk051[10]).induced.toList, (Generated.hostChunk051[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 1, 0, 5, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 3, 0, 3, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0622]

theorem fixed_values_0623 :
    (fixedDensityCounts (maskGraph 7 44856), fixedComplementCounts (maskGraph 7 44856)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 6, 0, 2, 0, 4, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0623_semantics :
    ((Generated.hostChunk051[11]).induced.toList, (Generated.hostChunk051[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk051[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk051[11]).mask)) := by
  have hm : (Generated.hostChunk051[11]).mask = 44856 := by decide +kernel
  have hv : ((Generated.hostChunk051[11]).induced.toList, (Generated.hostChunk051[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 6, 0, 2, 0, 4, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0623]

theorem fixed_chunk_051_semantics :
    ∀ h ∈ Generated.hostChunk051.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk051.toList = [Generated.hostChunk051[0], Generated.hostChunk051[1], Generated.hostChunk051[2], Generated.hostChunk051[3], Generated.hostChunk051[4], Generated.hostChunk051[5], Generated.hostChunk051[6], Generated.hostChunk051[7], Generated.hostChunk051[8], Generated.hostChunk051[9], Generated.hostChunk051[10], Generated.hostChunk051[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0612_semantics
  · exact fixed_host_0613_semantics
  · exact fixed_host_0614_semantics
  · exact fixed_host_0615_semantics
  · exact fixed_host_0616_semantics
  · exact fixed_host_0617_semantics
  · exact fixed_host_0618_semantics
  · exact fixed_host_0619_semantics
  · exact fixed_host_0620_semantics
  · exact fixed_host_0621_semantics
  · exact fixed_host_0622_semantics
  · exact fixed_host_0623_semantics

end InducedPentagons.Paper

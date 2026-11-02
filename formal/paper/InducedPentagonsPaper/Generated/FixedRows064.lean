import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData064
import InducedPentagonsPaper.Generated.FixedRows056

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0768 :
    (fixedDensityCounts (maskGraph 7 61177), fixedComplementCounts (maskGraph 7 61177)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 4, 0, 0, 2, 3, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0768_semantics :
    ((Generated.hostChunk064[0]).induced.toList, (Generated.hostChunk064[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[0]).mask)) := by
  have hm : (Generated.hostChunk064[0]).mask = 61177 := by decide +kernel
  have hv : ((Generated.hostChunk064[0]).induced.toList, (Generated.hostChunk064[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 4, 0, 0, 2, 3, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0768]

theorem fixed_values_0769 :
    (fixedDensityCounts (maskGraph 7 61179), fixedComplementCounts (maskGraph 7 61179)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 2, 2, 0, 0, 4, 0, 1, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0769_semantics :
    ((Generated.hostChunk064[1]).induced.toList, (Generated.hostChunk064[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[1]).mask)) := by
  have hm : (Generated.hostChunk064[1]).mask = 61179 := by decide +kernel
  have hv : ((Generated.hostChunk064[1]).induced.toList, (Generated.hostChunk064[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 2, 2, 0, 0, 4, 0, 1, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0769]

theorem fixed_values_0770 :
    (fixedDensityCounts (maskGraph 7 61180), fixedComplementCounts (maskGraph 7 61180)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 2, 1, 0, 0, 2, 2, 0, 1, 0, 4, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0770_semantics :
    ((Generated.hostChunk064[2]).induced.toList, (Generated.hostChunk064[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[2]).mask)) := by
  have hm : (Generated.hostChunk064[2]).mask = 61180 := by decide +kernel
  have hv : ((Generated.hostChunk064[2]).induced.toList, (Generated.hostChunk064[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 2, 1, 0, 0, 2, 2, 0, 1, 0, 4, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0770]

theorem fixed_values_0771 :
    (fixedDensityCounts (maskGraph 7 61181), fixedComplementCounts (maskGraph 7 61181)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0, 4, 0, 0, 0, 2, 3, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0771_semantics :
    ((Generated.hostChunk064[3]).induced.toList, (Generated.hostChunk064[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[3]).mask)) := by
  have hm : (Generated.hostChunk064[3]).mask = 61181 := by decide +kernel
  have hv : ((Generated.hostChunk064[3]).induced.toList, (Generated.hostChunk064[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0, 4, 0, 0, 0, 2, 3, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0771]

theorem fixed_values_0772 :
    (fixedDensityCounts (maskGraph 7 61183), fixedComplementCounts (maskGraph 7 61183)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 0, 2, 2, 0, 0, 0, 4, 0, 1, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0772_semantics :
    ((Generated.hostChunk064[4]).induced.toList, (Generated.hostChunk064[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[4]).mask)) := by
  have hm : (Generated.hostChunk064[4]).mask = 61183 := by decide +kernel
  have hv : ((Generated.hostChunk064[4]).induced.toList, (Generated.hostChunk064[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 2, 0, 3, 0, 0, 0, 2, 2, 0, 0, 0, 4, 0, 1, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0772]

theorem fixed_values_0773 :
    (fixedDensityCounts (maskGraph 7 61244), fixedComplementCounts (maskGraph 7 61244)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 8, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0773_semantics :
    ((Generated.hostChunk064[5]).induced.toList, (Generated.hostChunk064[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[5]).mask)) := by
  have hm : (Generated.hostChunk064[5]).mask = 61244 := by decide +kernel
  have hv : ((Generated.hostChunk064[5]).induced.toList, (Generated.hostChunk064[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 8, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0773]

theorem fixed_values_0774 :
    (fixedDensityCounts (maskGraph 7 61245), fixedComplementCounts (maskGraph 7 61245)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 1, 1, 1, 0, 0, 0, 3, 0, 0, 2, 4, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0774_semantics :
    ((Generated.hostChunk064[6]).induced.toList, (Generated.hostChunk064[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[6]).mask)) := by
  have hm : (Generated.hostChunk064[6]).mask = 61245 := by decide +kernel
  have hv : ((Generated.hostChunk064[6]).induced.toList, (Generated.hostChunk064[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 1, 1, 1, 0, 0, 0, 3, 0, 0, 2, 4, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0774]

theorem fixed_values_0775 :
    (fixedDensityCounts (maskGraph 7 61247), fixedComplementCounts (maskGraph 7 61247)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 9, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0775_semantics :
    ((Generated.hostChunk064[7]).induced.toList, (Generated.hostChunk064[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[7]).mask)) := by
  have hm : (Generated.hostChunk064[7]).mask = 61247 := by decide +kernel
  have hv : ((Generated.hostChunk064[7]).induced.toList, (Generated.hostChunk064[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 9, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0775]

theorem fixed_values_0776 :
    (fixedDensityCounts (maskGraph 7 61308), fixedComplementCounts (maskGraph 7 61308)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0776_semantics :
    ((Generated.hostChunk064[8]).induced.toList, (Generated.hostChunk064[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[8]).mask)) := by
  have hm : (Generated.hostChunk064[8]).mask = 61308 := by decide +kernel
  have hv : ((Generated.hostChunk064[8]).induced.toList, (Generated.hostChunk064[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0776]

theorem fixed_values_0777 :
    (fixedDensityCounts (maskGraph 7 61309), fixedComplementCounts (maskGraph 7 61309)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 4, 4, 3, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0777_semantics :
    ((Generated.hostChunk064[9]).induced.toList, (Generated.hostChunk064[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[9]).mask)) := by
  have hm : (Generated.hostChunk064[9]).mask = 61309 := by decide +kernel
  have hv : ((Generated.hostChunk064[9]).induced.toList, (Generated.hostChunk064[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 4, 4, 3, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0777]

theorem fixed_values_0778 :
    (fixedDensityCounts (maskGraph 7 61311), fixedComplementCounts (maskGraph 7 61311)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0778_semantics :
    ((Generated.hostChunk064[10]).induced.toList, (Generated.hostChunk064[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[10]).mask)) := by
  have hm : (Generated.hostChunk064[10]).mask = 61311 := by decide +kernel
  have hv : ((Generated.hostChunk064[10]).induced.toList, (Generated.hostChunk064[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0778]

theorem fixed_values_0779 :
    (fixedDensityCounts (maskGraph 7 61372), fixedComplementCounts (maskGraph 7 61372)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 4, 1, 7, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0779_semantics :
    ((Generated.hostChunk064[11]).induced.toList, (Generated.hostChunk064[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk064[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk064[11]).mask)) := by
  have hm : (Generated.hostChunk064[11]).mask = 61372 := by decide +kernel
  have hv : ((Generated.hostChunk064[11]).induced.toList, (Generated.hostChunk064[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 4, 1, 7, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0779]

theorem fixed_chunk_064_semantics :
    ∀ h ∈ Generated.hostChunk064.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk064.toList = [Generated.hostChunk064[0], Generated.hostChunk064[1], Generated.hostChunk064[2], Generated.hostChunk064[3], Generated.hostChunk064[4], Generated.hostChunk064[5], Generated.hostChunk064[6], Generated.hostChunk064[7], Generated.hostChunk064[8], Generated.hostChunk064[9], Generated.hostChunk064[10], Generated.hostChunk064[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0768_semantics
  · exact fixed_host_0769_semantics
  · exact fixed_host_0770_semantics
  · exact fixed_host_0771_semantics
  · exact fixed_host_0772_semantics
  · exact fixed_host_0773_semantics
  · exact fixed_host_0774_semantics
  · exact fixed_host_0775_semantics
  · exact fixed_host_0776_semantics
  · exact fixed_host_0777_semantics
  · exact fixed_host_0778_semantics
  · exact fixed_host_0779_semantics

end InducedPentagons.Paper

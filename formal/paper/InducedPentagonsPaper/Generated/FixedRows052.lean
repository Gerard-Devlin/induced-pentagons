import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData052
import InducedPentagonsPaper.Generated.FixedRows044

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0624 :
    (fixedDensityCounts (maskGraph 7 44857), fixedComplementCounts (maskGraph 7 44857)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 2, 4, 0, 0, 0, 0, 1, 0, 1, 2, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0624_semantics :
    ((Generated.hostChunk052[0]).induced.toList, (Generated.hostChunk052[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[0]).mask)) := by
  have hm : (Generated.hostChunk052[0]).mask = 44857 := by decide +kernel
  have hv : ((Generated.hostChunk052[0]).induced.toList, (Generated.hostChunk052[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 2, 4, 0, 0, 0, 0, 1, 0, 1, 2, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0624]

theorem fixed_values_0625 :
    (fixedDensityCounts (maskGraph 7 44858), fixedComplementCounts (maskGraph 7 44858)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 1, 0, 3, 2, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0625_semantics :
    ((Generated.hostChunk052[1]).induced.toList, (Generated.hostChunk052[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[1]).mask)) := by
  have hm : (Generated.hostChunk052[1]).mask = 44858 := by decide +kernel
  have hv : ((Generated.hostChunk052[1]).induced.toList, (Generated.hostChunk052[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 1, 0, 3, 2, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0625]

theorem fixed_values_0626 :
    (fixedDensityCounts (maskGraph 7 44859), fixedComplementCounts (maskGraph 7 44859)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 2, 1, 1, 1, 0, 1, 0, 0, 1, 3, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0626_semantics :
    ((Generated.hostChunk052[2]).induced.toList, (Generated.hostChunk052[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[2]).mask)) := by
  have hm : (Generated.hostChunk052[2]).mask = 44859 := by decide +kernel
  have hv : ((Generated.hostChunk052[2]).induced.toList, (Generated.hostChunk052[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 2, 1, 1, 1, 0, 1, 0, 0, 1, 3, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0626]

theorem fixed_values_0627 :
    (fixedDensityCounts (maskGraph 7 44862), fixedComplementCounts (maskGraph 7 44862)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 2, 0, 2, 2, 1, 0, 0, 0, 1, 2, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0627_semantics :
    ((Generated.hostChunk052[3]).induced.toList, (Generated.hostChunk052[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[3]).mask)) := by
  have hm : (Generated.hostChunk052[3]).mask = 44862 := by decide +kernel
  have hv : ((Generated.hostChunk052[3]).induced.toList, (Generated.hostChunk052[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 2, 0, 2, 2, 1, 0, 0, 0, 1, 2, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0627]

theorem fixed_values_0628 :
    (fixedDensityCounts (maskGraph 7 44863), fixedComplementCounts (maskGraph 7 44863)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 2, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 7, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0628_semantics :
    ((Generated.hostChunk052[4]).induced.toList, (Generated.hostChunk052[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[4]).mask)) := by
  have hm : (Generated.hostChunk052[4]).mask = 44863 := by decide +kernel
  have hv : ((Generated.hostChunk052[4]).induced.toList, (Generated.hostChunk052[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 2, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 7, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0628]

theorem fixed_values_0629 :
    (fixedDensityCounts (maskGraph 7 44922), fixedComplementCounts (maskGraph 7 44922)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 2, 5, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0629_semantics :
    ((Generated.hostChunk052[5]).induced.toList, (Generated.hostChunk052[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[5]).mask)) := by
  have hm : (Generated.hostChunk052[5]).mask = 44922 := by decide +kernel
  have hv : ((Generated.hostChunk052[5]).induced.toList, (Generated.hostChunk052[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 2, 5, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0629]

theorem fixed_values_0630 :
    (fixedDensityCounts (maskGraph 7 44923), fixedComplementCounts (maskGraph 7 44923)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 2, 2, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0630_semantics :
    ((Generated.hostChunk052[6]).induced.toList, (Generated.hostChunk052[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[6]).mask)) := by
  have hm : (Generated.hostChunk052[6]).mask = 44923 := by decide +kernel
  have hv : ((Generated.hostChunk052[6]).induced.toList, (Generated.hostChunk052[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 2, 2, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0630]

theorem fixed_values_0631 :
    (fixedDensityCounts (maskGraph 7 44924), fixedComplementCounts (maskGraph 7 44924)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 2, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0631_semantics :
    ((Generated.hostChunk052[7]).induced.toList, (Generated.hostChunk052[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[7]).mask)) := by
  have hm : (Generated.hostChunk052[7]).mask = 44924 := by decide +kernel
  have hv : ((Generated.hostChunk052[7]).induced.toList, (Generated.hostChunk052[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 2, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0631]

theorem fixed_values_0632 :
    (fixedDensityCounts (maskGraph 7 44925), fixedComplementCounts (maskGraph 7 44925)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 4, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0632_semantics :
    ((Generated.hostChunk052[8]).induced.toList, (Generated.hostChunk052[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[8]).mask)) := by
  have hm : (Generated.hostChunk052[8]).mask = 44925 := by decide +kernel
  have hv : ((Generated.hostChunk052[8]).induced.toList, (Generated.hostChunk052[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 4, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0632]

theorem fixed_values_0633 :
    (fixedDensityCounts (maskGraph 7 44926), fixedComplementCounts (maskGraph 7 44926)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0633_semantics :
    ((Generated.hostChunk052[9]).induced.toList, (Generated.hostChunk052[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[9]).mask)) := by
  have hm : (Generated.hostChunk052[9]).mask = 44926 := by decide +kernel
  have hv : ((Generated.hostChunk052[9]).induced.toList, (Generated.hostChunk052[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0633]

theorem fixed_values_0634 :
    (fixedDensityCounts (maskGraph 7 44927), fixedComplementCounts (maskGraph 7 44927)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0634_semantics :
    ((Generated.hostChunk052[10]).induced.toList, (Generated.hostChunk052[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[10]).mask)) := by
  have hm : (Generated.hostChunk052[10]).mask = 44927 := by decide +kernel
  have hv : ((Generated.hostChunk052[10]).induced.toList, (Generated.hostChunk052[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0634]

theorem fixed_values_0635 :
    (fixedDensityCounts (maskGraph 7 45054), fixedComplementCounts (maskGraph 7 45054)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0635_semantics :
    ((Generated.hostChunk052[11]).induced.toList, (Generated.hostChunk052[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk052[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk052[11]).mask)) := by
  have hm : (Generated.hostChunk052[11]).mask = 45054 := by decide +kernel
  have hv : ((Generated.hostChunk052[11]).induced.toList, (Generated.hostChunk052[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0635]

theorem fixed_chunk_052_semantics :
    ∀ h ∈ Generated.hostChunk052.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk052.toList = [Generated.hostChunk052[0], Generated.hostChunk052[1], Generated.hostChunk052[2], Generated.hostChunk052[3], Generated.hostChunk052[4], Generated.hostChunk052[5], Generated.hostChunk052[6], Generated.hostChunk052[7], Generated.hostChunk052[8], Generated.hostChunk052[9], Generated.hostChunk052[10], Generated.hostChunk052[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0624_semantics
  · exact fixed_host_0625_semantics
  · exact fixed_host_0626_semantics
  · exact fixed_host_0627_semantics
  · exact fixed_host_0628_semantics
  · exact fixed_host_0629_semantics
  · exact fixed_host_0630_semantics
  · exact fixed_host_0631_semantics
  · exact fixed_host_0632_semantics
  · exact fixed_host_0633_semantics
  · exact fixed_host_0634_semantics
  · exact fixed_host_0635_semantics

end InducedPentagons.Paper

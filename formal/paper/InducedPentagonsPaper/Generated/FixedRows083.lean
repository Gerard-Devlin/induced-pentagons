import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData083
import InducedPentagonsPaper.Generated.FixedRows075

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0996 :
    (fixedDensityCounts (maskGraph 7 380796), fixedComplementCounts (maskGraph 7 380796)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 11, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 7, 0, 2, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0996_semantics :
    ((Generated.hostChunk083[0]).induced.toList, (Generated.hostChunk083[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[0]).mask)) := by
  have hm : (Generated.hostChunk083[0]).mask = 380796 := by decide +kernel
  have hv : ((Generated.hostChunk083[0]).induced.toList, (Generated.hostChunk083[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 11, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 7, 0, 2, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0996]

theorem fixed_values_0997 :
    (fixedDensityCounts (maskGraph 7 380797), fixedComplementCounts (maskGraph 7 380797)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 1, 0, 4, 4, 4, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 4, 2, 2, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0997_semantics :
    ((Generated.hostChunk083[1]).induced.toList, (Generated.hostChunk083[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[1]).mask)) := by
  have hm : (Generated.hostChunk083[1]).mask = 380797 := by decide +kernel
  have hv : ((Generated.hostChunk083[1]).induced.toList, (Generated.hostChunk083[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 3, 1, 0, 4, 4, 4, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 4, 2, 2, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0997]

theorem fixed_values_0998 :
    (fixedDensityCounts (maskGraph 7 380798), fixedComplementCounts (maskGraph 7 380798)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 4, 3, 7, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 3, 4, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0998_semantics :
    ((Generated.hostChunk083[2]).induced.toList, (Generated.hostChunk083[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[2]).mask)) := by
  have hm : (Generated.hostChunk083[2]).mask = 380798 := by decide +kernel
  have hv : ((Generated.hostChunk083[2]).induced.toList, (Generated.hostChunk083[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 4, 3, 7, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 3, 4, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0998]

theorem fixed_values_0999 :
    (fixedDensityCounts (maskGraph 7 380799), fixedComplementCounts (maskGraph 7 380799)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 2, 4, 1, 6, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 2, 1, 5, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0999_semantics :
    ((Generated.hostChunk083[3]).induced.toList, (Generated.hostChunk083[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[3]).mask)) := by
  have hm : (Generated.hostChunk083[3]).mask = 380799 := by decide +kernel
  have hv : ((Generated.hostChunk083[3]).induced.toList, (Generated.hostChunk083[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 2, 4, 1, 6, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 2, 1, 5, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0999]

theorem fixed_values_1000 :
    (fixedDensityCounts (maskGraph 7 380863), fixedComplementCounts (maskGraph 7 380863)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 1, 0, 2, 4, 0, 6, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 2, 4, 0, 2, 1, 0, 1]) := by
  decide +kernel

theorem fixed_host_1000_semantics :
    ((Generated.hostChunk083[4]).induced.toList, (Generated.hostChunk083[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[4]).mask)) := by
  have hm : (Generated.hostChunk083[4]).mask = 380863 := by decide +kernel
  have hv : ((Generated.hostChunk083[4]).induced.toList, (Generated.hostChunk083[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 1, 0, 2, 4, 0, 6, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 2, 4, 0, 2, 1, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1000]

theorem fixed_values_1001 :
    (fixedDensityCounts (maskGraph 7 380926), fixedComplementCounts (maskGraph 7 380926)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 4, 6, 2, 3, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 4, 3, 2, 1, 1, 0]) := by
  decide +kernel

theorem fixed_host_1001_semantics :
    ((Generated.hostChunk083[5]).induced.toList, (Generated.hostChunk083[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[5]).mask)) := by
  have hm : (Generated.hostChunk083[5]).mask = 380926 := by decide +kernel
  have hv : ((Generated.hostChunk083[5]).induced.toList, (Generated.hostChunk083[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 4, 6, 2, 3, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 4, 3, 2, 1, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1001]

theorem fixed_values_1002 :
    (fixedDensityCounts (maskGraph 7 380927), fixedComplementCounts (maskGraph 7 380927)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 4, 0, 8, 0, 3, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 4, 0, 5, 0, 1, 1]) := by
  decide +kernel

theorem fixed_host_1002_semantics :
    ((Generated.hostChunk083[6]).induced.toList, (Generated.hostChunk083[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[6]).mask)) := by
  have hm : (Generated.hostChunk083[6]).mask = 380927 := by decide +kernel
  have hv : ((Generated.hostChunk083[6]).induced.toList, (Generated.hostChunk083[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 4, 0, 8, 0, 3, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 0, 4, 0, 5, 0, 1, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1002]

theorem fixed_values_1003 :
    (fixedDensityCounts (maskGraph 7 384501), fixedComplementCounts (maskGraph 7 384501)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 1, 4, 5, 0, 3, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 2, 3, 0, 2, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_1003_semantics :
    ((Generated.hostChunk083[7]).induced.toList, (Generated.hostChunk083[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[7]).mask)) := by
  have hm : (Generated.hostChunk083[7]).mask = 384501 := by decide +kernel
  have hv : ((Generated.hostChunk083[7]).induced.toList, (Generated.hostChunk083[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 1, 4, 5, 0, 3, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 2, 3, 0, 2, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1003]

theorem fixed_values_1004 :
    (fixedDensityCounts (maskGraph 7 384503), fixedComplementCounts (maskGraph 7 384503)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 2, 4, 1, 4, 2, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 2, 2, 0, 3, 2, 1, 0]) := by
  decide +kernel

theorem fixed_host_1004_semantics :
    ((Generated.hostChunk083[8]).induced.toList, (Generated.hostChunk083[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[8]).mask)) := by
  have hm : (Generated.hostChunk083[8]).mask = 384503 := by decide +kernel
  have hv : ((Generated.hostChunk083[8]).induced.toList, (Generated.hostChunk083[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 2, 4, 1, 4, 2, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 2, 2, 0, 3, 2, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1004]

theorem fixed_values_1005 :
    (fixedDensityCounts (maskGraph 7 384511), fixedComplementCounts (maskGraph 7 384511)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 6, 0, 4, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 2, 0, 4, 0]) := by
  decide +kernel

theorem fixed_host_1005_semantics :
    ((Generated.hostChunk083[9]).induced.toList, (Generated.hostChunk083[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[9]).mask)) := by
  have hm : (Generated.hostChunk083[9]).mask = 384511 := by decide +kernel
  have hv : ((Generated.hostChunk083[9]).induced.toList, (Generated.hostChunk083[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 6, 0, 4, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4, 0, 2, 0, 4, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1005]

theorem fixed_values_1006 :
    (fixedDensityCounts (maskGraph 7 384697), fixedComplementCounts (maskGraph 7 384697)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 2, 8, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 4, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_1006_semantics :
    ((Generated.hostChunk083[10]).induced.toList, (Generated.hostChunk083[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[10]).mask)) := by
  have hm : (Generated.hostChunk083[10]).mask = 384697 := by decide +kernel
  have hv : ((Generated.hostChunk083[10]).induced.toList, (Generated.hostChunk083[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 2, 8, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 4, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1006]

theorem fixed_values_1007 :
    (fixedDensityCounts (maskGraph 7 384699), fixedComplementCounts (maskGraph 7 384699)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 4, 8, 3, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 7, 1, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_1007_semantics :
    ((Generated.hostChunk083[11]).induced.toList, (Generated.hostChunk083[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk083[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk083[11]).mask)) := by
  have hm : (Generated.hostChunk083[11]).mask = 384699 := by decide +kernel
  have hv : ((Generated.hostChunk083[11]).induced.toList, (Generated.hostChunk083[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 4, 8, 3, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 7, 1, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1007]

theorem fixed_chunk_083_semantics :
    ∀ h ∈ Generated.hostChunk083.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk083.toList = [Generated.hostChunk083[0], Generated.hostChunk083[1], Generated.hostChunk083[2], Generated.hostChunk083[3], Generated.hostChunk083[4], Generated.hostChunk083[5], Generated.hostChunk083[6], Generated.hostChunk083[7], Generated.hostChunk083[8], Generated.hostChunk083[9], Generated.hostChunk083[10], Generated.hostChunk083[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0996_semantics
  · exact fixed_host_0997_semantics
  · exact fixed_host_0998_semantics
  · exact fixed_host_0999_semantics
  · exact fixed_host_1000_semantics
  · exact fixed_host_1001_semantics
  · exact fixed_host_1002_semantics
  · exact fixed_host_1003_semantics
  · exact fixed_host_1004_semantics
  · exact fixed_host_1005_semantics
  · exact fixed_host_1006_semantics
  · exact fixed_host_1007_semantics

end InducedPentagons.Paper

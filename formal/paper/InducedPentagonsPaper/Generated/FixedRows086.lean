import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData086
import InducedPentagonsPaper.Generated.FixedRows078

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_1032 :
    (fixedDensityCounts (maskGraph 7 454655), fixedComplementCounts (maskGraph 7 454655)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 7, 2, 6, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 5, 2, 4, 1]) := by
  decide +kernel

theorem fixed_host_1032_semantics :
    ((Generated.hostChunk086[0]).induced.toList, (Generated.hostChunk086[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[0]).mask)) := by
  have hm : (Generated.hostChunk086[0]).mask = 454655 := by decide +kernel
  have hv : ((Generated.hostChunk086[0]).induced.toList, (Generated.hostChunk086[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 7, 2, 6, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 5, 2, 4, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1032]

theorem fixed_values_1033 :
    (fixedDensityCounts (maskGraph 7 458685), fixedComplementCounts (maskGraph 7 458685)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 5, 4, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 4, 4, 2, 0]) := by
  decide +kernel

theorem fixed_host_1033_semantics :
    ((Generated.hostChunk086[1]).induced.toList, (Generated.hostChunk086[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[1]).mask)) := by
  have hm : (Generated.hostChunk086[1]).mask = 458685 := by decide +kernel
  have hv : ((Generated.hostChunk086[1]).induced.toList, (Generated.hostChunk086[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 5, 4, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 4, 4, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1033]

theorem fixed_values_1034 :
    (fixedDensityCounts (maskGraph 7 458687), fixedComplementCounts (maskGraph 7 458687)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 4, 5, 7, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 3, 6, 0]) := by
  decide +kernel

theorem fixed_host_1034_semantics :
    ((Generated.hostChunk086[2]).induced.toList, (Generated.hostChunk086[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[2]).mask)) := by
  have hm : (Generated.hostChunk086[2]).mask = 458687 := by decide +kernel
  have hv : ((Generated.hostChunk086[2]).induced.toList, (Generated.hostChunk086[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 4, 5, 7, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 3, 6, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1034]

theorem fixed_values_1035 :
    (fixedDensityCounts (maskGraph 7 458751), fixedComplementCounts (maskGraph 7 458751)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 9, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 7, 2]) := by
  decide +kernel

theorem fixed_host_1035_semantics :
    ((Generated.hostChunk086[3]).induced.toList, (Generated.hostChunk086[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[3]).mask)) := by
  have hm : (Generated.hostChunk086[3]).mask = 458751 := by decide +kernel
  have hv : ((Generated.hostChunk086[3]).induced.toList, (Generated.hostChunk086[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 9, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 7, 2]) := by decide +kernel
  rw [hm, hv, fixed_values_1035]

theorem fixed_values_1036 :
    (fixedDensityCounts (maskGraph 7 522111), fixedComplementCounts (maskGraph 7 522111)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 4, 4, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 1]) := by
  decide +kernel

theorem fixed_host_1036_semantics :
    ((Generated.hostChunk086[4]).induced.toList, (Generated.hostChunk086[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[4]).mask)) := by
  have hm : (Generated.hostChunk086[4]).mask = 522111 := by decide +kernel
  have hv : ((Generated.hostChunk086[4]).induced.toList, (Generated.hostChunk086[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 4, 4, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_1036]

theorem fixed_values_1037 :
    (fixedDensityCounts (maskGraph 7 522238), fixedComplementCounts (maskGraph 7 522238)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 11, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 4, 0]) := by
  decide +kernel

theorem fixed_host_1037_semantics :
    ((Generated.hostChunk086[5]).induced.toList, (Generated.hostChunk086[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[5]).mask)) := by
  have hm : (Generated.hostChunk086[5]).mask = 522238 := by decide +kernel
  have hv : ((Generated.hostChunk086[5]).induced.toList, (Generated.hostChunk086[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 11, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 4, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1037]

theorem fixed_values_1038 :
    (fixedDensityCounts (maskGraph 7 522239), fixedComplementCounts (maskGraph 7 522239)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 4, 9, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 7, 2]) := by
  decide +kernel

theorem fixed_host_1038_semantics :
    ((Generated.hostChunk086[6]).induced.toList, (Generated.hostChunk086[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[6]).mask)) := by
  have hm : (Generated.hostChunk086[6]).mask = 522239 := by decide +kernel
  have hv : ((Generated.hostChunk086[6]).induced.toList, (Generated.hostChunk086[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 4, 9, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 7, 2]) := by decide +kernel
  rw [hm, hv, fixed_values_1038]

theorem fixed_values_1039 :
    (fixedDensityCounts (maskGraph 7 524287), fixedComplementCounts (maskGraph 7 524287)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 8, 7], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 8, 5]) := by
  decide +kernel

theorem fixed_host_1039_semantics :
    ((Generated.hostChunk086[7]).induced.toList, (Generated.hostChunk086[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[7]).mask)) := by
  have hm : (Generated.hostChunk086[7]).mask = 524287 := by decide +kernel
  have hv : ((Generated.hostChunk086[7]).induced.toList, (Generated.hostChunk086[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 8, 7], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 8, 5]) := by decide +kernel
  rw [hm, hv, fixed_values_1039]

theorem fixed_values_1040 :
    (fixedDensityCounts (maskGraph 7 1015743), fixedComplementCounts (maskGraph 7 1015743)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 12, 0]) := by
  decide +kernel

theorem fixed_host_1040_semantics :
    ((Generated.hostChunk086[8]).induced.toList, (Generated.hostChunk086[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[8]).mask)) := by
  have hm : (Generated.hostChunk086[8]).mask = 1015743 := by decide +kernel
  have hv : ((Generated.hostChunk086[8]).induced.toList, (Generated.hostChunk086[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 12, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1040]

theorem fixed_values_1041 :
    (fixedDensityCounts (maskGraph 7 1015807), fixedComplementCounts (maskGraph 7 1015807)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 14, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 12, 4]) := by
  decide +kernel

theorem fixed_host_1041_semantics :
    ((Generated.hostChunk086[9]).induced.toList, (Generated.hostChunk086[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[9]).mask)) := by
  have hm : (Generated.hostChunk086[9]).mask = 1015807 := by decide +kernel
  have hv : ((Generated.hostChunk086[9]).induced.toList, (Generated.hostChunk086[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 14, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 12, 4]) := by decide +kernel
  rw [hm, hv, fixed_values_1041]

theorem fixed_values_1042 :
    (fixedDensityCounts (maskGraph 7 1048575), fixedComplementCounts (maskGraph 7 1048575)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10]) := by
  decide +kernel

theorem fixed_host_1042_semantics :
    ((Generated.hostChunk086[10]).induced.toList, (Generated.hostChunk086[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[10]).mask)) := by
  have hm : (Generated.hostChunk086[10]).mask = 1048575 := by decide +kernel
  have hv : ((Generated.hostChunk086[10]).induced.toList, (Generated.hostChunk086[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10]) := by decide +kernel
  rw [hm, hv, fixed_values_1042]

theorem fixed_values_1043 :
    (fixedDensityCounts (maskGraph 7 2097151), fixedComplementCounts (maskGraph 7 2097151)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21]) := by
  decide +kernel

theorem fixed_host_1043_semantics :
    ((Generated.hostChunk086[11]).induced.toList, (Generated.hostChunk086[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk086[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk086[11]).mask)) := by
  have hm : (Generated.hostChunk086[11]).mask = 2097151 := by decide +kernel
  have hv : ((Generated.hostChunk086[11]).induced.toList, (Generated.hostChunk086[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21]) := by decide +kernel
  rw [hm, hv, fixed_values_1043]

theorem fixed_chunk_086_semantics :
    ∀ h ∈ Generated.hostChunk086.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk086.toList = [Generated.hostChunk086[0], Generated.hostChunk086[1], Generated.hostChunk086[2], Generated.hostChunk086[3], Generated.hostChunk086[4], Generated.hostChunk086[5], Generated.hostChunk086[6], Generated.hostChunk086[7], Generated.hostChunk086[8], Generated.hostChunk086[9], Generated.hostChunk086[10], Generated.hostChunk086[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_1032_semantics
  · exact fixed_host_1033_semantics
  · exact fixed_host_1034_semantics
  · exact fixed_host_1035_semantics
  · exact fixed_host_1036_semantics
  · exact fixed_host_1037_semantics
  · exact fixed_host_1038_semantics
  · exact fixed_host_1039_semantics
  · exact fixed_host_1040_semantics
  · exact fixed_host_1041_semantics
  · exact fixed_host_1042_semantics
  · exact fixed_host_1043_semantics

end InducedPentagons.Paper

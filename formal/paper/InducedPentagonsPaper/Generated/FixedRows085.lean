import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData085
import InducedPentagonsPaper.Generated.FixedRows077

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_1020 :
    (fixedDensityCounts (maskGraph 7 393151), fixedComplementCounts (maskGraph 7 393151)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 6, 3, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 6, 3, 1, 2]) := by
  decide +kernel

theorem fixed_host_1020_semantics :
    ((Generated.hostChunk085[0]).induced.toList, (Generated.hostChunk085[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[0]).mask)) := by
  have hm : (Generated.hostChunk085[0]).mask = 393151 := by decide +kernel
  have hv : ((Generated.hostChunk085[0]).induced.toList, (Generated.hostChunk085[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 6, 3, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 6, 3, 1, 2]) := by decide +kernel
  rw [hm, hv, fixed_values_1020]

theorem fixed_values_1021 :
    (fixedDensityCounts (maskGraph 7 393215), fixedComplementCounts (maskGraph 7 393215)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 9, 0, 3, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 9, 0, 3, 3]) := by
  decide +kernel

theorem fixed_host_1021_semantics :
    ((Generated.hostChunk085[1]).induced.toList, (Generated.hostChunk085[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[1]).mask)) := by
  have hm : (Generated.hostChunk085[1]).mask = 393215 := by decide +kernel
  have hv : ((Generated.hostChunk085[1]).induced.toList, (Generated.hostChunk085[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 9, 0, 3, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 9, 0, 3, 3]) := by decide +kernel
  rw [hm, hv, fixed_values_1021]

theorem fixed_values_1022 :
    (fixedDensityCounts (maskGraph 7 425917), fixedComplementCounts (maskGraph 7 425917)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 6, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 6, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_1022_semantics :
    ((Generated.hostChunk085[2]).induced.toList, (Generated.hostChunk085[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[2]).mask)) := by
  have hm : (Generated.hostChunk085[2]).mask = 425917 := by decide +kernel
  have hv : ((Generated.hostChunk085[2]).induced.toList, (Generated.hostChunk085[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 6, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 6, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1022]

theorem fixed_values_1023 :
    (fixedDensityCounts (maskGraph 7 425919), fixedComplementCounts (maskGraph 7 425919)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 8, 4, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 8, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_1023_semantics :
    ((Generated.hostChunk085[3]).induced.toList, (Generated.hostChunk085[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[3]).mask)) := by
  have hm : (Generated.hostChunk085[3]).mask = 425919 := by decide +kernel
  have hv : ((Generated.hostChunk085[3]).induced.toList, (Generated.hostChunk085[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 8, 4, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 8, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1023]

theorem fixed_values_1024 :
    (fixedDensityCounts (maskGraph 7 425983), fixedComplementCounts (maskGraph 7 425983)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 12, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 12, 0, 0, 2]) := by
  decide +kernel

theorem fixed_host_1024_semantics :
    ((Generated.hostChunk085[4]).induced.toList, (Generated.hostChunk085[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[4]).mask)) := by
  have hm : (Generated.hostChunk085[4]).mask = 425983 := by decide +kernel
  have hv : ((Generated.hostChunk085[4]).induced.toList, (Generated.hostChunk085[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 12, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 12, 0, 0, 2]) := by decide +kernel
  rw [hm, hv, fixed_values_1024]

theorem fixed_values_1025 :
    (fixedDensityCounts (maskGraph 7 452606), fixedComplementCounts (maskGraph 7 452606)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 5, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 5, 0, 0]) := by
  decide +kernel

theorem fixed_host_1025_semantics :
    ((Generated.hostChunk085[5]).induced.toList, (Generated.hostChunk085[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[5]).mask)) := by
  have hm : (Generated.hostChunk085[5]).mask = 452606 := by decide +kernel
  have hv : ((Generated.hostChunk085[5]).induced.toList, (Generated.hostChunk085[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 5, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 5, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1025]

theorem fixed_values_1026 :
    (fixedDensityCounts (maskGraph 7 452607), fixedComplementCounts (maskGraph 7 452607)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 0, 5, 0, 5, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 0, 0, 0, 5, 0]) := by
  decide +kernel

theorem fixed_host_1026_semantics :
    ((Generated.hostChunk085[6]).induced.toList, (Generated.hostChunk085[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[6]).mask)) := by
  have hm : (Generated.hostChunk085[6]).mask = 452607 := by decide +kernel
  have hv : ((Generated.hostChunk085[6]).induced.toList, (Generated.hostChunk085[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 0, 5, 0, 5, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 0, 0, 0, 5, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1026]

theorem fixed_values_1027 :
    (fixedDensityCounts (maskGraph 7 454463), fixedComplementCounts (maskGraph 7 454463)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 6, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 3, 0, 0]) := by
  decide +kernel

theorem fixed_host_1027_semantics :
    ((Generated.hostChunk085[7]).induced.toList, (Generated.hostChunk085[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[7]).mask)) := by
  have hm : (Generated.hostChunk085[7]).mask = 454463 := by decide +kernel
  have hv : ((Generated.hostChunk085[7]).induced.toList, (Generated.hostChunk085[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 6, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 3, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1027]

theorem fixed_values_1028 :
    (fixedDensityCounts (maskGraph 7 454524), fixedComplementCounts (maskGraph 7 454524)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_1028_semantics :
    ((Generated.hostChunk085[8]).induced.toList, (Generated.hostChunk085[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[8]).mask)) := by
  have hm : (Generated.hostChunk085[8]).mask = 454524 := by decide +kernel
  have hv : ((Generated.hostChunk085[8]).induced.toList, (Generated.hostChunk085[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1028]

theorem fixed_values_1029 :
    (fixedDensityCounts (maskGraph 7 454525), fixedComplementCounts (maskGraph 7 454525)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 6, 3, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 3, 3, 0, 0]) := by
  decide +kernel

theorem fixed_host_1029_semantics :
    ((Generated.hostChunk085[9]).induced.toList, (Generated.hostChunk085[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[9]).mask)) := by
  have hm : (Generated.hostChunk085[9]).mask = 454525 := by decide +kernel
  have hv : ((Generated.hostChunk085[9]).induced.toList, (Generated.hostChunk085[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 6, 3, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 3, 3, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1029]

theorem fixed_values_1030 :
    (fixedDensityCounts (maskGraph 7 454527), fixedComplementCounts (maskGraph 7 454527)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 2, 6, 3, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 4, 2, 3, 0]) := by
  decide +kernel

theorem fixed_host_1030_semantics :
    ((Generated.hostChunk085[10]).induced.toList, (Generated.hostChunk085[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[10]).mask)) := by
  have hm : (Generated.hostChunk085[10]).mask = 454527 := by decide +kernel
  have hv : ((Generated.hostChunk085[10]).induced.toList, (Generated.hostChunk085[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 2, 6, 3, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 4, 2, 3, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1030]

theorem fixed_values_1031 :
    (fixedDensityCounts (maskGraph 7 454654), fixedComplementCounts (maskGraph 7 454654)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 3, 4, 8, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 4, 6, 1, 0]) := by
  decide +kernel

theorem fixed_host_1031_semantics :
    ((Generated.hostChunk085[11]).induced.toList, (Generated.hostChunk085[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk085[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk085[11]).mask)) := by
  have hm : (Generated.hostChunk085[11]).mask = 454654 := by decide +kernel
  have hv : ((Generated.hostChunk085[11]).induced.toList, (Generated.hostChunk085[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 3, 4, 8, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 4, 6, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_1031]

theorem fixed_chunk_085_semantics :
    ∀ h ∈ Generated.hostChunk085.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk085.toList = [Generated.hostChunk085[0], Generated.hostChunk085[1], Generated.hostChunk085[2], Generated.hostChunk085[3], Generated.hostChunk085[4], Generated.hostChunk085[5], Generated.hostChunk085[6], Generated.hostChunk085[7], Generated.hostChunk085[8], Generated.hostChunk085[9], Generated.hostChunk085[10], Generated.hostChunk085[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_1020_semantics
  · exact fixed_host_1021_semantics
  · exact fixed_host_1022_semantics
  · exact fixed_host_1023_semantics
  · exact fixed_host_1024_semantics
  · exact fixed_host_1025_semantics
  · exact fixed_host_1026_semantics
  · exact fixed_host_1027_semantics
  · exact fixed_host_1028_semantics
  · exact fixed_host_1029_semantics
  · exact fixed_host_1030_semantics
  · exact fixed_host_1031_semantics

end InducedPentagons.Paper

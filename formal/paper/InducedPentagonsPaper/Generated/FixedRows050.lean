import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData050
import InducedPentagonsPaper.Generated.FixedRows042

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0600 :
    (fixedDensityCounts (maskGraph 7 44467), fixedComplementCounts (maskGraph 7 44467)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0600_semantics :
    ((Generated.hostChunk050[0]).induced.toList, (Generated.hostChunk050[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[0]).mask)) := by
  have hm : (Generated.hostChunk050[0]).mask = 44467 := by decide +kernel
  have hv : ((Generated.hostChunk050[0]).induced.toList, (Generated.hostChunk050[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0600]

theorem fixed_values_0601 :
    (fixedDensityCounts (maskGraph 7 44470), fixedComplementCounts (maskGraph 7 44470)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 3, 2, 1, 1, 0, 0, 0, 1, 3, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0601_semantics :
    ((Generated.hostChunk050[1]).induced.toList, (Generated.hostChunk050[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[1]).mask)) := by
  have hm : (Generated.hostChunk050[1]).mask = 44470 := by decide +kernel
  have hv : ((Generated.hostChunk050[1]).induced.toList, (Generated.hostChunk050[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 3, 2, 1, 1, 0, 0, 0, 1, 3, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0601]

theorem fixed_values_0602 :
    (fixedDensityCounts (maskGraph 7 44471), fixedComplementCounts (maskGraph 7 44471)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 1, 4, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0602_semantics :
    ((Generated.hostChunk050[2]).induced.toList, (Generated.hostChunk050[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[2]).mask)) := by
  have hm : (Generated.hostChunk050[2]).mask = 44471 := by decide +kernel
  have hv : ((Generated.hostChunk050[2]).induced.toList, (Generated.hostChunk050[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 1, 4, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0602]

theorem fixed_values_0603 :
    (fixedDensityCounts (maskGraph 7 44472), fixedComplementCounts (maskGraph 7 44472)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 1, 0, 8, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0603_semantics :
    ((Generated.hostChunk050[3]).induced.toList, (Generated.hostChunk050[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[3]).mask)) := by
  have hm : (Generated.hostChunk050[3]).mask = 44472 := by decide +kernel
  have hv : ((Generated.hostChunk050[3]).induced.toList, (Generated.hostChunk050[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 1, 0, 8, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0603]

theorem fixed_values_0604 :
    (fixedDensityCounts (maskGraph 7 44473), fixedComplementCounts (maskGraph 7 44473)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0604_semantics :
    ((Generated.hostChunk050[4]).induced.toList, (Generated.hostChunk050[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[4]).mask)) := by
  have hm : (Generated.hostChunk050[4]).mask = 44473 := by decide +kernel
  have hv : ((Generated.hostChunk050[4]).induced.toList, (Generated.hostChunk050[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0604]

theorem fixed_values_0605 :
    (fixedDensityCounts (maskGraph 7 44474), fixedComplementCounts (maskGraph 7 44474)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 2, 3, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0605_semantics :
    ((Generated.hostChunk050[5]).induced.toList, (Generated.hostChunk050[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[5]).mask)) := by
  have hm : (Generated.hostChunk050[5]).mask = 44474 := by decide +kernel
  have hv : ((Generated.hostChunk050[5]).induced.toList, (Generated.hostChunk050[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 2, 3, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0605]

theorem fixed_values_0606 :
    (fixedDensityCounts (maskGraph 7 44475), fixedComplementCounts (maskGraph 7 44475)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 3, 1, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0606_semantics :
    ((Generated.hostChunk050[6]).induced.toList, (Generated.hostChunk050[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[6]).mask)) := by
  have hm : (Generated.hostChunk050[6]).mask = 44475 := by decide +kernel
  have hv : ((Generated.hostChunk050[6]).induced.toList, (Generated.hostChunk050[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 3, 1, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 3, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0606]

theorem fixed_values_0607 :
    (fixedDensityCounts (maskGraph 7 44476), fixedComplementCounts (maskGraph 7 44476)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 3, 2, 5, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0607_semantics :
    ((Generated.hostChunk050[7]).induced.toList, (Generated.hostChunk050[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[7]).mask)) := by
  have hm : (Generated.hostChunk050[7]).mask = 44476 := by decide +kernel
  have hv : ((Generated.hostChunk050[7]).induced.toList, (Generated.hostChunk050[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 3, 2, 5, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0607]

theorem fixed_values_0608 :
    (fixedDensityCounts (maskGraph 7 44477), fixedComplementCounts (maskGraph 7 44477)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 2, 1, 2, 0, 0, 0, 0, 3, 1, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0608_semantics :
    ((Generated.hostChunk050[8]).induced.toList, (Generated.hostChunk050[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[8]).mask)) := by
  have hm : (Generated.hostChunk050[8]).mask = 44477 := by decide +kernel
  have hv : ((Generated.hostChunk050[8]).induced.toList, (Generated.hostChunk050[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 2, 1, 2, 0, 0, 0, 0, 3, 1, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0608]

theorem fixed_values_0609 :
    (fixedDensityCounts (maskGraph 7 44478), fixedComplementCounts (maskGraph 7 44478)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 0, 0, 1, 1, 3, 2, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0609_semantics :
    ((Generated.hostChunk050[9]).induced.toList, (Generated.hostChunk050[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[9]).mask)) := by
  have hm : (Generated.hostChunk050[9]).mask = 44478 := by decide +kernel
  have hv : ((Generated.hostChunk050[9]).induced.toList, (Generated.hostChunk050[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 0, 0, 1, 1, 3, 2, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0609]

theorem fixed_values_0610 :
    (fixedDensityCounts (maskGraph 7 44479), fixedComplementCounts (maskGraph 7 44479)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 0, 0, 1, 1, 0, 5, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 3, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0610_semantics :
    ((Generated.hostChunk050[10]).induced.toList, (Generated.hostChunk050[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[10]).mask)) := by
  have hm : (Generated.hostChunk050[10]).mask = 44479 := by decide +kernel
  have hv : ((Generated.hostChunk050[10]).induced.toList, (Generated.hostChunk050[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 0, 0, 1, 1, 0, 5, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 3, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0610]

theorem fixed_values_0611 :
    (fixedDensityCounts (maskGraph 7 44526), fixedComplementCounts (maskGraph 7 44526)) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 2, 1, 0, 2, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0611_semantics :
    ((Generated.hostChunk050[11]).induced.toList, (Generated.hostChunk050[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk050[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk050[11]).mask)) := by
  have hm : (Generated.hostChunk050[11]).mask = 44526 := by decide +kernel
  have hv : ((Generated.hostChunk050[11]).induced.toList, (Generated.hostChunk050[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 2, 1, 0, 2, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0611]

theorem fixed_chunk_050_semantics :
    ∀ h ∈ Generated.hostChunk050.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk050.toList = [Generated.hostChunk050[0], Generated.hostChunk050[1], Generated.hostChunk050[2], Generated.hostChunk050[3], Generated.hostChunk050[4], Generated.hostChunk050[5], Generated.hostChunk050[6], Generated.hostChunk050[7], Generated.hostChunk050[8], Generated.hostChunk050[9], Generated.hostChunk050[10], Generated.hostChunk050[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0600_semantics
  · exact fixed_host_0601_semantics
  · exact fixed_host_0602_semantics
  · exact fixed_host_0603_semantics
  · exact fixed_host_0604_semantics
  · exact fixed_host_0605_semantics
  · exact fixed_host_0606_semantics
  · exact fixed_host_0607_semantics
  · exact fixed_host_0608_semantics
  · exact fixed_host_0609_semantics
  · exact fixed_host_0610_semantics
  · exact fixed_host_0611_semantics

end InducedPentagons.Paper

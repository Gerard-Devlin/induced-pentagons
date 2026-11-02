import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData036
import InducedPentagonsPaper.Generated.FixedRows028

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0432 :
    (fixedDensityCounts (maskGraph 7 39673), fixedComplementCounts (maskGraph 7 39673)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 2, 1, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 3, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0432_semantics :
    ((Generated.hostChunk036[0]).induced.toList, (Generated.hostChunk036[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[0]).mask)) := by
  have hm : (Generated.hostChunk036[0]).mask = 39673 := by decide +kernel
  have hv : ((Generated.hostChunk036[0]).induced.toList, (Generated.hostChunk036[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 2, 1, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 3, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0432]

theorem fixed_values_0433 :
    (fixedDensityCounts (maskGraph 7 39674), fixedComplementCounts (maskGraph 7 39674)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 3, 1, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0433_semantics :
    ((Generated.hostChunk036[1]).induced.toList, (Generated.hostChunk036[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[1]).mask)) := by
  have hm : (Generated.hostChunk036[1]).mask = 39674 := by decide +kernel
  have hv : ((Generated.hostChunk036[1]).induced.toList, (Generated.hostChunk036[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 3, 1, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0433]

theorem fixed_values_0434 :
    (fixedDensityCounts (maskGraph 7 39675), fixedComplementCounts (maskGraph 7 39675)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0434_semantics :
    ((Generated.hostChunk036[2]).induced.toList, (Generated.hostChunk036[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[2]).mask)) := by
  have hm : (Generated.hostChunk036[2]).mask = 39675 := by decide +kernel
  have hv : ((Generated.hostChunk036[2]).induced.toList, (Generated.hostChunk036[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0434]

theorem fixed_values_0435 :
    (fixedDensityCounts (maskGraph 7 39678), fixedComplementCounts (maskGraph 7 39678)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 3, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0435_semantics :
    ((Generated.hostChunk036[3]).induced.toList, (Generated.hostChunk036[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[3]).mask)) := by
  have hm : (Generated.hostChunk036[3]).mask = 39678 := by decide +kernel
  have hv : ((Generated.hostChunk036[3]).induced.toList, (Generated.hostChunk036[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 3, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0435]

theorem fixed_values_0436 :
    (fixedDensityCounts (maskGraph 7 39679), fixedComplementCounts (maskGraph 7 39679)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0436_semantics :
    ((Generated.hostChunk036[4]).induced.toList, (Generated.hostChunk036[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[4]).mask)) := by
  have hm : (Generated.hostChunk036[4]).mask = 39679 := by decide +kernel
  have hv : ((Generated.hostChunk036[4]).induced.toList, (Generated.hostChunk036[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0436]

theorem fixed_values_0437 :
    (fixedDensityCounts (maskGraph 7 39902), fixedComplementCounts (maskGraph 7 39902)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0437_semantics :
    ((Generated.hostChunk036[5]).induced.toList, (Generated.hostChunk036[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[5]).mask)) := by
  have hm : (Generated.hostChunk036[5]).mask = 39902 := by decide +kernel
  have hv : ((Generated.hostChunk036[5]).induced.toList, (Generated.hostChunk036[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0437]

theorem fixed_values_0438 :
    (fixedDensityCounts (maskGraph 7 39903), fixedComplementCounts (maskGraph 7 39903)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0438_semantics :
    ((Generated.hostChunk036[6]).induced.toList, (Generated.hostChunk036[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[6]).mask)) := by
  have hm : (Generated.hostChunk036[6]).mask = 39903 := by decide +kernel
  have hv : ((Generated.hostChunk036[6]).induced.toList, (Generated.hostChunk036[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0438]

theorem fixed_values_0439 :
    (fixedDensityCounts (maskGraph 7 39918), fixedComplementCounts (maskGraph 7 39918)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0439_semantics :
    ((Generated.hostChunk036[7]).induced.toList, (Generated.hostChunk036[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[7]).mask)) := by
  have hm : (Generated.hostChunk036[7]).mask = 39918 := by decide +kernel
  have hv : ((Generated.hostChunk036[7]).induced.toList, (Generated.hostChunk036[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0439]

theorem fixed_values_0440 :
    (fixedDensityCounts (maskGraph 7 39919), fixedComplementCounts (maskGraph 7 39919)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0440_semantics :
    ((Generated.hostChunk036[8]).induced.toList, (Generated.hostChunk036[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[8]).mask)) := by
  have hm : (Generated.hostChunk036[8]).mask = 39919 := by decide +kernel
  have hv : ((Generated.hostChunk036[8]).induced.toList, (Generated.hostChunk036[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0440]

theorem fixed_values_0441 :
    (fixedDensityCounts (maskGraph 7 39920), fixedComplementCounts (maskGraph 7 39920)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 5, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0441_semantics :
    ((Generated.hostChunk036[9]).induced.toList, (Generated.hostChunk036[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[9]).mask)) := by
  have hm : (Generated.hostChunk036[9]).mask = 39920 := by decide +kernel
  have hv : ((Generated.hostChunk036[9]).induced.toList, (Generated.hostChunk036[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 5, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0441]

theorem fixed_values_0442 :
    (fixedDensityCounts (maskGraph 7 39921), fixedComplementCounts (maskGraph 7 39921)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 2, 3, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0442_semantics :
    ((Generated.hostChunk036[10]).induced.toList, (Generated.hostChunk036[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[10]).mask)) := by
  have hm : (Generated.hostChunk036[10]).mask = 39921 := by decide +kernel
  have hv : ((Generated.hostChunk036[10]).induced.toList, (Generated.hostChunk036[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 2, 3, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0442]

theorem fixed_values_0443 :
    (fixedDensityCounts (maskGraph 7 39922), fixedComplementCounts (maskGraph 7 39922)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 1, 5, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0443_semantics :
    ((Generated.hostChunk036[11]).induced.toList, (Generated.hostChunk036[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk036[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk036[11]).mask)) := by
  have hm : (Generated.hostChunk036[11]).mask = 39922 := by decide +kernel
  have hv : ((Generated.hostChunk036[11]).induced.toList, (Generated.hostChunk036[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 1, 5, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0443]

theorem fixed_chunk_036_semantics :
    ∀ h ∈ Generated.hostChunk036.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk036.toList = [Generated.hostChunk036[0], Generated.hostChunk036[1], Generated.hostChunk036[2], Generated.hostChunk036[3], Generated.hostChunk036[4], Generated.hostChunk036[5], Generated.hostChunk036[6], Generated.hostChunk036[7], Generated.hostChunk036[8], Generated.hostChunk036[9], Generated.hostChunk036[10], Generated.hostChunk036[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0432_semantics
  · exact fixed_host_0433_semantics
  · exact fixed_host_0434_semantics
  · exact fixed_host_0435_semantics
  · exact fixed_host_0436_semantics
  · exact fixed_host_0437_semantics
  · exact fixed_host_0438_semantics
  · exact fixed_host_0439_semantics
  · exact fixed_host_0440_semantics
  · exact fixed_host_0441_semantics
  · exact fixed_host_0442_semantics
  · exact fixed_host_0443_semantics

end InducedPentagons.Paper

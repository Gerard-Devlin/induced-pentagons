import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData015
import InducedPentagonsPaper.Generated.FixedRows007

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0180 :
    (fixedDensityCounts (maskGraph 7 3903), fixedComplementCounts (maskGraph 7 3903)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0180_semantics :
    ((Generated.hostChunk015[0]).induced.toList, (Generated.hostChunk015[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[0]).mask)) := by
  have hm : (Generated.hostChunk015[0]).mask = 3903 := by decide +kernel
  have hv : ((Generated.hostChunk015[0]).induced.toList, (Generated.hostChunk015[0]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0180]

theorem fixed_values_0181 :
    (fixedDensityCounts (maskGraph 7 3962), fixedComplementCounts (maskGraph 7 3962)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0181_semantics :
    ((Generated.hostChunk015[1]).induced.toList, (Generated.hostChunk015[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[1]).mask)) := by
  have hm : (Generated.hostChunk015[1]).mask = 3962 := by decide +kernel
  have hv : ((Generated.hostChunk015[1]).induced.toList, (Generated.hostChunk015[1]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0181]

theorem fixed_values_0182 :
    (fixedDensityCounts (maskGraph 7 3963), fixedComplementCounts (maskGraph 7 3963)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0182_semantics :
    ((Generated.hostChunk015[2]).induced.toList, (Generated.hostChunk015[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[2]).mask)) := by
  have hm : (Generated.hostChunk015[2]).mask = 3963 := by decide +kernel
  have hv : ((Generated.hostChunk015[2]).induced.toList, (Generated.hostChunk015[2]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0182]

theorem fixed_values_0183 :
    (fixedDensityCounts (maskGraph 7 3964), fixedComplementCounts (maskGraph 7 3964)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0183_semantics :
    ((Generated.hostChunk015[3]).induced.toList, (Generated.hostChunk015[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[3]).mask)) := by
  have hm : (Generated.hostChunk015[3]).mask = 3964 := by decide +kernel
  have hv : ((Generated.hostChunk015[3]).induced.toList, (Generated.hostChunk015[3]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0183]

theorem fixed_values_0184 :
    (fixedDensityCounts (maskGraph 7 3965), fixedComplementCounts (maskGraph 7 3965)) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0184_semantics :
    ((Generated.hostChunk015[4]).induced.toList, (Generated.hostChunk015[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[4]).mask)) := by
  have hm : (Generated.hostChunk015[4]).mask = 3965 := by decide +kernel
  have hv : ((Generated.hostChunk015[4]).induced.toList, (Generated.hostChunk015[4]).complement.toList) =
      ([0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0184]

theorem fixed_values_0185 :
    (fixedDensityCounts (maskGraph 7 3966), fixedComplementCounts (maskGraph 7 3966)) =
      ([0, 1, 0, 1, 3, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0185_semantics :
    ((Generated.hostChunk015[5]).induced.toList, (Generated.hostChunk015[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[5]).mask)) := by
  have hm : (Generated.hostChunk015[5]).mask = 3966 := by decide +kernel
  have hv : ((Generated.hostChunk015[5]).induced.toList, (Generated.hostChunk015[5]).complement.toList) =
      ([0, 1, 0, 1, 3, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0185]

theorem fixed_values_0186 :
    (fixedDensityCounts (maskGraph 7 3967), fixedComplementCounts (maskGraph 7 3967)) =
      ([0, 1, 0, 1, 3, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0186_semantics :
    ((Generated.hostChunk015[6]).induced.toList, (Generated.hostChunk015[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[6]).mask)) := by
  have hm : (Generated.hostChunk015[6]).mask = 3967 := by decide +kernel
  have hv : ((Generated.hostChunk015[6]).induced.toList, (Generated.hostChunk015[6]).complement.toList) =
      ([0, 1, 0, 1, 3, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0186]

theorem fixed_values_0187 :
    (fixedDensityCounts (maskGraph 7 4094), fixedComplementCounts (maskGraph 7 4094)) =
      ([0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0187_semantics :
    ((Generated.hostChunk015[7]).induced.toList, (Generated.hostChunk015[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[7]).mask)) := by
  have hm : (Generated.hostChunk015[7]).mask = 4094 := by decide +kernel
  have hv : ((Generated.hostChunk015[7]).induced.toList, (Generated.hostChunk015[7]).complement.toList) =
      ([0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0187]

theorem fixed_values_0188 :
    (fixedDensityCounts (maskGraph 7 4095), fixedComplementCounts (maskGraph 7 4095)) =
      ([0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0188_semantics :
    ((Generated.hostChunk015[8]).induced.toList, (Generated.hostChunk015[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[8]).mask)) := by
  have hm : (Generated.hostChunk015[8]).mask = 4095 := by decide +kernel
  have hv : ((Generated.hostChunk015[8]).induced.toList, (Generated.hostChunk015[8]).complement.toList) =
      ([0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0188]

theorem fixed_values_0189 :
    (fixedDensityCounts (maskGraph 7 6543), fixedComplementCounts (maskGraph 7 6543)) =
      ([0, 0, 6, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0189_semantics :
    ((Generated.hostChunk015[9]).induced.toList, (Generated.hostChunk015[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[9]).mask)) := by
  have hm : (Generated.hostChunk015[9]).mask = 6543 := by decide +kernel
  have hv : ((Generated.hostChunk015[9]).induced.toList, (Generated.hostChunk015[9]).complement.toList) =
      ([0, 0, 6, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0189]

theorem fixed_values_0190 :
    (fixedDensityCounts (maskGraph 7 6549), fixedComplementCounts (maskGraph 7 6549)) =
      ([0, 0, 6, 0, 0, 0, 1, 4, 3, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0190_semantics :
    ((Generated.hostChunk015[10]).induced.toList, (Generated.hostChunk015[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[10]).mask)) := by
  have hm : (Generated.hostChunk015[10]).mask = 6549 := by decide +kernel
  have hv : ((Generated.hostChunk015[10]).induced.toList, (Generated.hostChunk015[10]).complement.toList) =
      ([0, 0, 6, 0, 0, 0, 1, 4, 3, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0190]

theorem fixed_values_0191 :
    (fixedDensityCounts (maskGraph 7 6551), fixedComplementCounts (maskGraph 7 6551)) =
      ([0, 0, 5, 1, 0, 0, 0, 2, 4, 0, 0, 0, 3, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0191_semantics :
    ((Generated.hostChunk015[11]).induced.toList, (Generated.hostChunk015[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk015[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk015[11]).mask)) := by
  have hm : (Generated.hostChunk015[11]).mask = 6551 := by decide +kernel
  have hv : ((Generated.hostChunk015[11]).induced.toList, (Generated.hostChunk015[11]).complement.toList) =
      ([0, 0, 5, 1, 0, 0, 0, 2, 4, 0, 0, 0, 3, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0191]

theorem fixed_chunk_015_semantics :
    ∀ h ∈ Generated.hostChunk015.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk015.toList = [Generated.hostChunk015[0], Generated.hostChunk015[1], Generated.hostChunk015[2], Generated.hostChunk015[3], Generated.hostChunk015[4], Generated.hostChunk015[5], Generated.hostChunk015[6], Generated.hostChunk015[7], Generated.hostChunk015[8], Generated.hostChunk015[9], Generated.hostChunk015[10], Generated.hostChunk015[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0180_semantics
  · exact fixed_host_0181_semantics
  · exact fixed_host_0182_semantics
  · exact fixed_host_0183_semantics
  · exact fixed_host_0184_semantics
  · exact fixed_host_0185_semantics
  · exact fixed_host_0186_semantics
  · exact fixed_host_0187_semantics
  · exact fixed_host_0188_semantics
  · exact fixed_host_0189_semantics
  · exact fixed_host_0190_semantics
  · exact fixed_host_0191_semantics

end InducedPentagons.Paper

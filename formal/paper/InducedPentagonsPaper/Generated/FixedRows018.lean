import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData018
import InducedPentagonsPaper.Generated.FixedRows010

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0216 :
    (fixedDensityCounts (maskGraph 7 6809), fixedComplementCounts (maskGraph 7 6809)) =
      ([0, 0, 3, 0, 0, 1, 2, 7, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0216_semantics :
    ((Generated.hostChunk018[0]).induced.toList, (Generated.hostChunk018[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[0]).mask)) := by
  have hm : (Generated.hostChunk018[0]).mask = 6809 := by decide +kernel
  have hv : ((Generated.hostChunk018[0]).induced.toList, (Generated.hostChunk018[0]).complement.toList) =
      ([0, 0, 3, 0, 0, 1, 2, 7, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0216]

theorem fixed_values_0217 :
    (fixedDensityCounts (maskGraph 7 6811), fixedComplementCounts (maskGraph 7 6811)) =
      ([0, 0, 3, 0, 0, 0, 1, 4, 6, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0217_semantics :
    ((Generated.hostChunk018[1]).induced.toList, (Generated.hostChunk018[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[1]).mask)) := by
  have hm : (Generated.hostChunk018[1]).mask = 6811 := by decide +kernel
  have hv : ((Generated.hostChunk018[1]).induced.toList, (Generated.hostChunk018[1]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 1, 4, 6, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0217]

theorem fixed_values_0218 :
    (fixedDensityCounts (maskGraph 7 6812), fixedComplementCounts (maskGraph 7 6812)) =
      ([0, 0, 4, 2, 0, 0, 1, 6, 0, 0, 0, 0, 2, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0218_semantics :
    ((Generated.hostChunk018[2]).induced.toList, (Generated.hostChunk018[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[2]).mask)) := by
  have hm : (Generated.hostChunk018[2]).mask = 6812 := by decide +kernel
  have hv : ((Generated.hostChunk018[2]).induced.toList, (Generated.hostChunk018[2]).complement.toList) =
      ([0, 0, 4, 2, 0, 0, 1, 6, 0, 0, 0, 0, 2, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0218]

theorem fixed_values_0219 :
    (fixedDensityCounts (maskGraph 7 6813), fixedComplementCounts (maskGraph 7 6813)) =
      ([0, 0, 2, 1, 0, 1, 1, 5, 3, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0219_semantics :
    ((Generated.hostChunk018[3]).induced.toList, (Generated.hostChunk018[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[3]).mask)) := by
  have hm : (Generated.hostChunk018[3]).mask = 6813 := by decide +kernel
  have hv : ((Generated.hostChunk018[3]).induced.toList, (Generated.hostChunk018[3]).complement.toList) =
      ([0, 0, 2, 1, 0, 1, 1, 5, 3, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0219]

theorem fixed_values_0220 :
    (fixedDensityCounts (maskGraph 7 6815), fixedComplementCounts (maskGraph 7 6815)) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 6, 0, 0, 0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0220_semantics :
    ((Generated.hostChunk018[4]).induced.toList, (Generated.hostChunk018[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[4]).mask)) := by
  have hm : (Generated.hostChunk018[4]).mask = 6815 := by decide +kernel
  have hv : ((Generated.hostChunk018[4]).induced.toList, (Generated.hostChunk018[4]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 6, 0, 0, 0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0220]

theorem fixed_values_0221 :
    (fixedDensityCounts (maskGraph 7 6820), fixedComplementCounts (maskGraph 7 6820)) =
      ([0, 0, 3, 0, 0, 0, 6, 6, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0221_semantics :
    ((Generated.hostChunk018[5]).induced.toList, (Generated.hostChunk018[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[5]).mask)) := by
  have hm : (Generated.hostChunk018[5]).mask = 6820 := by decide +kernel
  have hv : ((Generated.hostChunk018[5]).induced.toList, (Generated.hostChunk018[5]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 6, 6, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0221]

theorem fixed_values_0222 :
    (fixedDensityCounts (maskGraph 7 6821), fixedComplementCounts (maskGraph 7 6821)) =
      ([0, 0, 3, 0, 0, 0, 2, 6, 2, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0222_semantics :
    ((Generated.hostChunk018[6]).induced.toList, (Generated.hostChunk018[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[6]).mask)) := by
  have hm : (Generated.hostChunk018[6]).mask = 6821 := by decide +kernel
  have hv : ((Generated.hostChunk018[6]).induced.toList, (Generated.hostChunk018[6]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 2, 6, 2, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0222]

theorem fixed_values_0223 :
    (fixedDensityCounts (maskGraph 7 6823), fixedComplementCounts (maskGraph 7 6823)) =
      ([0, 0, 3, 0, 0, 0, 1, 4, 4, 0, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0223_semantics :
    ((Generated.hostChunk018[7]).induced.toList, (Generated.hostChunk018[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[7]).mask)) := by
  have hm : (Generated.hostChunk018[7]).mask = 6823 := by decide +kernel
  have hv : ((Generated.hostChunk018[7]).induced.toList, (Generated.hostChunk018[7]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 1, 4, 4, 0, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0223]

theorem fixed_values_0224 :
    (fixedDensityCounts (maskGraph 7 6824), fixedComplementCounts (maskGraph 7 6824)) =
      ([0, 0, 3, 0, 0, 0, 3, 6, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0224_semantics :
    ((Generated.hostChunk018[8]).induced.toList, (Generated.hostChunk018[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[8]).mask)) := by
  have hm : (Generated.hostChunk018[8]).mask = 6824 := by decide +kernel
  have hv : ((Generated.hostChunk018[8]).induced.toList, (Generated.hostChunk018[8]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 3, 6, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0224]

theorem fixed_values_0225 :
    (fixedDensityCounts (maskGraph 7 6825), fixedComplementCounts (maskGraph 7 6825)) =
      ([0, 0, 3, 0, 0, 0, 2, 5, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0225_semantics :
    ((Generated.hostChunk018[9]).induced.toList, (Generated.hostChunk018[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[9]).mask)) := by
  have hm : (Generated.hostChunk018[9]).mask = 6825 := by decide +kernel
  have hv : ((Generated.hostChunk018[9]).induced.toList, (Generated.hostChunk018[9]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 2, 5, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0225]

theorem fixed_values_0226 :
    (fixedDensityCounts (maskGraph 7 6826), fixedComplementCounts (maskGraph 7 6826)) =
      ([0, 0, 3, 0, 0, 0, 1, 3, 3, 5, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0226_semantics :
    ((Generated.hostChunk018[10]).induced.toList, (Generated.hostChunk018[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[10]).mask)) := by
  have hm : (Generated.hostChunk018[10]).mask = 6826 := by decide +kernel
  have hv : ((Generated.hostChunk018[10]).induced.toList, (Generated.hostChunk018[10]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 1, 3, 3, 5, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0226]

theorem fixed_values_0227 :
    (fixedDensityCounts (maskGraph 7 6827), fixedComplementCounts (maskGraph 7 6827)) =
      ([0, 0, 3, 0, 0, 0, 1, 3, 2, 0, 5, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0227_semantics :
    ((Generated.hostChunk018[11]).induced.toList, (Generated.hostChunk018[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk018[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk018[11]).mask)) := by
  have hm : (Generated.hostChunk018[11]).mask = 6827 := by decide +kernel
  have hv : ((Generated.hostChunk018[11]).induced.toList, (Generated.hostChunk018[11]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 1, 3, 2, 0, 5, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0227]

theorem fixed_chunk_018_semantics :
    ∀ h ∈ Generated.hostChunk018.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk018.toList = [Generated.hostChunk018[0], Generated.hostChunk018[1], Generated.hostChunk018[2], Generated.hostChunk018[3], Generated.hostChunk018[4], Generated.hostChunk018[5], Generated.hostChunk018[6], Generated.hostChunk018[7], Generated.hostChunk018[8], Generated.hostChunk018[9], Generated.hostChunk018[10], Generated.hostChunk018[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0216_semantics
  · exact fixed_host_0217_semantics
  · exact fixed_host_0218_semantics
  · exact fixed_host_0219_semantics
  · exact fixed_host_0220_semantics
  · exact fixed_host_0221_semantics
  · exact fixed_host_0222_semantics
  · exact fixed_host_0223_semantics
  · exact fixed_host_0224_semantics
  · exact fixed_host_0225_semantics
  · exact fixed_host_0226_semantics
  · exact fixed_host_0227_semantics

end InducedPentagons.Paper

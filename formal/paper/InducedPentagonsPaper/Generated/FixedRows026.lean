import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData026
import InducedPentagonsPaper.Generated.FixedRows018

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0312 :
    (fixedDensityCounts (maskGraph 7 7931), fixedComplementCounts (maskGraph 7 7931)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 6, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0312_semantics :
    ((Generated.hostChunk026[0]).induced.toList, (Generated.hostChunk026[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[0]).mask)) := by
  have hm : (Generated.hostChunk026[0]).mask = 7931 := by decide +kernel
  have hv : ((Generated.hostChunk026[0]).induced.toList, (Generated.hostChunk026[0]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 6, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0312]

theorem fixed_values_0313 :
    (fixedDensityCounts (maskGraph 7 7932), fixedComplementCounts (maskGraph 7 7932)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 2, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0313_semantics :
    ((Generated.hostChunk026[1]).induced.toList, (Generated.hostChunk026[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[1]).mask)) := by
  have hm : (Generated.hostChunk026[1]).mask = 7932 := by decide +kernel
  have hv : ((Generated.hostChunk026[1]).induced.toList, (Generated.hostChunk026[1]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 2, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0313]

theorem fixed_values_0314 :
    (fixedDensityCounts (maskGraph 7 7933), fixedComplementCounts (maskGraph 7 7933)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 2, 2, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0314_semantics :
    ((Generated.hostChunk026[2]).induced.toList, (Generated.hostChunk026[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[2]).mask)) := by
  have hm : (Generated.hostChunk026[2]).mask = 7933 := by decide +kernel
  have hv : ((Generated.hostChunk026[2]).induced.toList, (Generated.hostChunk026[2]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 2, 2, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0314]

theorem fixed_values_0315 :
    (fixedDensityCounts (maskGraph 7 7934), fixedComplementCounts (maskGraph 7 7934)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0315_semantics :
    ((Generated.hostChunk026[3]).induced.toList, (Generated.hostChunk026[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[3]).mask)) := by
  have hm : (Generated.hostChunk026[3]).mask = 7934 := by decide +kernel
  have hv : ((Generated.hostChunk026[3]).induced.toList, (Generated.hostChunk026[3]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0315]

theorem fixed_values_0316 :
    (fixedDensityCounts (maskGraph 7 7935), fixedComplementCounts (maskGraph 7 7935)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0316_semantics :
    ((Generated.hostChunk026[4]).induced.toList, (Generated.hostChunk026[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[4]).mask)) := by
  have hm : (Generated.hostChunk026[4]).mask = 7935 := by decide +kernel
  have hv : ((Generated.hostChunk026[4]).induced.toList, (Generated.hostChunk026[4]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0316]

theorem fixed_values_0317 :
    (fixedDensityCounts (maskGraph 7 8124), fixedComplementCounts (maskGraph 7 8124)) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 8, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0317_semantics :
    ((Generated.hostChunk026[5]).induced.toList, (Generated.hostChunk026[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[5]).mask)) := by
  have hm : (Generated.hostChunk026[5]).mask = 8124 := by decide +kernel
  have hv : ((Generated.hostChunk026[5]).induced.toList, (Generated.hostChunk026[5]).complement.toList) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 8, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0317]

theorem fixed_values_0318 :
    (fixedDensityCounts (maskGraph 7 8125), fixedComplementCounts (maskGraph 7 8125)) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 4, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0318_semantics :
    ((Generated.hostChunk026[6]).induced.toList, (Generated.hostChunk026[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[6]).mask)) := by
  have hm : (Generated.hostChunk026[6]).mask = 8125 := by decide +kernel
  have hv : ((Generated.hostChunk026[6]).induced.toList, (Generated.hostChunk026[6]).complement.toList) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 4, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0318]

theorem fixed_values_0319 :
    (fixedDensityCounts (maskGraph 7 8126), fixedComplementCounts (maskGraph 7 8126)) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 3, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0319_semantics :
    ((Generated.hostChunk026[7]).induced.toList, (Generated.hostChunk026[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[7]).mask)) := by
  have hm : (Generated.hostChunk026[7]).mask = 8126 := by decide +kernel
  have hv : ((Generated.hostChunk026[7]).induced.toList, (Generated.hostChunk026[7]).complement.toList) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 3, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0319]

theorem fixed_values_0320 :
    (fixedDensityCounts (maskGraph 7 8127), fixedComplementCounts (maskGraph 7 8127)) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0320_semantics :
    ((Generated.hostChunk026[8]).induced.toList, (Generated.hostChunk026[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[8]).mask)) := by
  have hm : (Generated.hostChunk026[8]).mask = 8127 := by decide +kernel
  have hv : ((Generated.hostChunk026[8]).induced.toList, (Generated.hostChunk026[8]).complement.toList) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0320]

theorem fixed_values_0321 :
    (fixedDensityCounts (maskGraph 7 8190), fixedComplementCounts (maskGraph 7 8190)) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0321_semantics :
    ((Generated.hostChunk026[9]).induced.toList, (Generated.hostChunk026[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[9]).mask)) := by
  have hm : (Generated.hostChunk026[9]).mask = 8190 := by decide +kernel
  have hv : ((Generated.hostChunk026[9]).induced.toList, (Generated.hostChunk026[9]).complement.toList) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0321]

theorem fixed_values_0322 :
    (fixedDensityCounts (maskGraph 7 8191), fixedComplementCounts (maskGraph 7 8191)) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0322_semantics :
    ((Generated.hostChunk026[10]).induced.toList, (Generated.hostChunk026[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[10]).mask)) := by
  have hm : (Generated.hostChunk026[10]).mask = 8191 := by decide +kernel
  have hv : ((Generated.hostChunk026[10]).induced.toList, (Generated.hostChunk026[10]).complement.toList) =
      ([0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0322]

theorem fixed_values_0323 :
    (fixedDensityCounts (maskGraph 7 15260), fixedComplementCounts (maskGraph 7 15260)) =
      ([0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0323_semantics :
    ((Generated.hostChunk026[11]).induced.toList, (Generated.hostChunk026[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk026[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk026[11]).mask)) := by
  have hm : (Generated.hostChunk026[11]).mask = 15260 := by decide +kernel
  have hv : ((Generated.hostChunk026[11]).induced.toList, (Generated.hostChunk026[11]).complement.toList) =
      ([0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0323]

theorem fixed_chunk_026_semantics :
    ∀ h ∈ Generated.hostChunk026.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk026.toList = [Generated.hostChunk026[0], Generated.hostChunk026[1], Generated.hostChunk026[2], Generated.hostChunk026[3], Generated.hostChunk026[4], Generated.hostChunk026[5], Generated.hostChunk026[6], Generated.hostChunk026[7], Generated.hostChunk026[8], Generated.hostChunk026[9], Generated.hostChunk026[10], Generated.hostChunk026[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0312_semantics
  · exact fixed_host_0313_semantics
  · exact fixed_host_0314_semantics
  · exact fixed_host_0315_semantics
  · exact fixed_host_0316_semantics
  · exact fixed_host_0317_semantics
  · exact fixed_host_0318_semantics
  · exact fixed_host_0319_semantics
  · exact fixed_host_0320_semantics
  · exact fixed_host_0321_semantics
  · exact fixed_host_0322_semantics
  · exact fixed_host_0323_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0000 :
    (fixedDensityCounts (maskGraph 7 0), fixedComplementCounts (maskGraph 7 0)) =
      ([21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0000_semantics :
    ((Generated.hostChunk000[0]).induced.toList, (Generated.hostChunk000[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[0]).mask)) := by
  have hm : (Generated.hostChunk000[0]).mask = 0 := by decide +kernel
  have hv : ((Generated.hostChunk000[0]).induced.toList, (Generated.hostChunk000[0]).complement.toList) =
      ([21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0000]

theorem fixed_values_0001 :
    (fixedDensityCounts (maskGraph 7 1), fixedComplementCounts (maskGraph 7 1)) =
      ([11, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0001_semantics :
    ((Generated.hostChunk000[1]).induced.toList, (Generated.hostChunk000[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[1]).mask)) := by
  have hm : (Generated.hostChunk000[1]).mask = 1 := by decide +kernel
  have hv : ((Generated.hostChunk000[1]).induced.toList, (Generated.hostChunk000[1]).complement.toList) =
      ([11, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0001]

theorem fixed_values_0002 :
    (fixedDensityCounts (maskGraph 7 3), fixedComplementCounts (maskGraph 7 3)) =
      ([7, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0002_semantics :
    ((Generated.hostChunk000[2]).induced.toList, (Generated.hostChunk000[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[2]).mask)) := by
  have hm : (Generated.hostChunk000[2]).mask = 3 := by decide +kernel
  have hv : ((Generated.hostChunk000[2]).induced.toList, (Generated.hostChunk000[2]).complement.toList) =
      ([7, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0002]

theorem fixed_values_0003 :
    (fixedDensityCounts (maskGraph 7 7), fixedComplementCounts (maskGraph 7 7)) =
      ([6, 3, 9, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0003_semantics :
    ((Generated.hostChunk000[3]).induced.toList, (Generated.hostChunk000[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[3]).mask)) := by
  have hm : (Generated.hostChunk000[3]).mask = 7 := by decide +kernel
  have hv : ((Generated.hostChunk000[3]).induced.toList, (Generated.hostChunk000[3]).complement.toList) =
      ([6, 3, 9, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0003]

theorem fixed_values_0004 :
    (fixedDensityCounts (maskGraph 7 15), fixedComplementCounts (maskGraph 7 15)) =
      ([6, 0, 6, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0004_semantics :
    ((Generated.hostChunk000[4]).induced.toList, (Generated.hostChunk000[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[4]).mask)) := by
  have hm : (Generated.hostChunk000[4]).mask = 15 := by decide +kernel
  have hv : ((Generated.hostChunk000[4]).induced.toList, (Generated.hostChunk000[4]).complement.toList) =
      ([6, 0, 6, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0004]

theorem fixed_values_0005 :
    (fixedDensityCounts (maskGraph 7 31), fixedComplementCounts (maskGraph 7 31)) =
      ([6, 0, 0, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0005_semantics :
    ((Generated.hostChunk000[5]).induced.toList, (Generated.hostChunk000[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[5]).mask)) := by
  have hm : (Generated.hostChunk000[5]).mask = 31 := by decide +kernel
  have hv : ((Generated.hostChunk000[5]).induced.toList, (Generated.hostChunk000[5]).complement.toList) =
      ([6, 0, 0, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0005]

theorem fixed_values_0006 :
    (fixedDensityCounts (maskGraph 7 63), fixedComplementCounts (maskGraph 7 63)) =
      ([6, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0006_semantics :
    ((Generated.hostChunk000[6]).induced.toList, (Generated.hostChunk000[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[6]).mask)) := by
  have hm : (Generated.hostChunk000[6]).mask = 63 := by decide +kernel
  have hv : ((Generated.hostChunk000[6]).induced.toList, (Generated.hostChunk000[6]).complement.toList) =
      ([6, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0006]

theorem fixed_values_0007 :
    (fixedDensityCounts (maskGraph 7 67), fixedComplementCounts (maskGraph 7 67)) =
      ([3, 12, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0007_semantics :
    ((Generated.hostChunk000[7]).induced.toList, (Generated.hostChunk000[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[7]).mask)) := by
  have hm : (Generated.hostChunk000[7]).mask = 67 := by decide +kernel
  have hv : ((Generated.hostChunk000[7]).induced.toList, (Generated.hostChunk000[7]).complement.toList) =
      ([3, 12, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0007]

theorem fixed_values_0008 :
    (fixedDensityCounts (maskGraph 7 68), fixedComplementCounts (maskGraph 7 68)) =
      ([4, 14, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0008_semantics :
    ((Generated.hostChunk000[8]).induced.toList, (Generated.hostChunk000[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[8]).mask)) := by
  have hm : (Generated.hostChunk000[8]).mask = 68 := by decide +kernel
  have hv : ((Generated.hostChunk000[8]).induced.toList, (Generated.hostChunk000[8]).complement.toList) =
      ([4, 14, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0008]

theorem fixed_values_0009 :
    (fixedDensityCounts (maskGraph 7 69), fixedComplementCounts (maskGraph 7 69)) =
      ([3, 9, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0009_semantics :
    ((Generated.hostChunk000[9]).induced.toList, (Generated.hostChunk000[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[9]).mask)) := by
  have hm : (Generated.hostChunk000[9]).mask = 69 := by decide +kernel
  have hv : ((Generated.hostChunk000[9]).induced.toList, (Generated.hostChunk000[9]).complement.toList) =
      ([3, 9, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0009]

theorem fixed_values_0010 :
    (fixedDensityCounts (maskGraph 7 71), fixedComplementCounts (maskGraph 7 71)) =
      ([2, 7, 6, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0010_semantics :
    ((Generated.hostChunk000[10]).induced.toList, (Generated.hostChunk000[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[10]).mask)) := by
  have hm : (Generated.hostChunk000[10]).mask = 71 := by decide +kernel
  have hv : ((Generated.hostChunk000[10]).induced.toList, (Generated.hostChunk000[10]).complement.toList) =
      ([2, 7, 6, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0010]

theorem fixed_values_0011 :
    (fixedDensityCounts (maskGraph 7 76), fixedComplementCounts (maskGraph 7 76)) =
      ([2, 9, 5, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0011_semantics :
    ((Generated.hostChunk000[11]).induced.toList, (Generated.hostChunk000[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk000[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk000[11]).mask)) := by
  have hm : (Generated.hostChunk000[11]).mask = 76 := by decide +kernel
  have hv : ((Generated.hostChunk000[11]).induced.toList, (Generated.hostChunk000[11]).complement.toList) =
      ([2, 9, 5, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0011]

theorem fixed_chunk_000_semantics :
    ∀ h ∈ Generated.hostChunk000.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk000.toList = [Generated.hostChunk000[0], Generated.hostChunk000[1], Generated.hostChunk000[2], Generated.hostChunk000[3], Generated.hostChunk000[4], Generated.hostChunk000[5], Generated.hostChunk000[6], Generated.hostChunk000[7], Generated.hostChunk000[8], Generated.hostChunk000[9], Generated.hostChunk000[10], Generated.hostChunk000[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0000_semantics
  · exact fixed_host_0001_semantics
  · exact fixed_host_0002_semantics
  · exact fixed_host_0003_semantics
  · exact fixed_host_0004_semantics
  · exact fixed_host_0005_semantics
  · exact fixed_host_0006_semantics
  · exact fixed_host_0007_semantics
  · exact fixed_host_0008_semantics
  · exact fixed_host_0009_semantics
  · exact fixed_host_0010_semantics
  · exact fixed_host_0011_semantics

end InducedPentagons.Paper

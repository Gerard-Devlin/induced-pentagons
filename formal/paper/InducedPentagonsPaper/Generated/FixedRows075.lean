import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData075
import InducedPentagonsPaper.Generated.FixedRows067

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0900 :
    (fixedDensityCounts (maskGraph 7 122623), fixedComplementCounts (maskGraph 7 122623)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0900_semantics :
    ((Generated.hostChunk075[0]).induced.toList, (Generated.hostChunk075[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[0]).mask)) := by
  have hm : (Generated.hostChunk075[0]).mask = 122623 := by decide +kernel
  have hv : ((Generated.hostChunk075[0]).induced.toList, (Generated.hostChunk075[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0900]

theorem fixed_values_0901 :
    (fixedDensityCounts (maskGraph 7 122681), fixedComplementCounts (maskGraph 7 122681)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 1, 0, 0, 2, 4, 0, 1, 2, 4, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 4, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0901_semantics :
    ((Generated.hostChunk075[1]).induced.toList, (Generated.hostChunk075[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[1]).mask)) := by
  have hm : (Generated.hostChunk075[1]).mask = 122681 := by decide +kernel
  have hv : ((Generated.hostChunk075[1]).induced.toList, (Generated.hostChunk075[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 1, 0, 0, 2, 4, 0, 1, 2, 4, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 4, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0901]

theorem fixed_values_0902 :
    (fixedDensityCounts (maskGraph 7 122682), fixedComplementCounts (maskGraph 7 122682)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 5, 1, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0902_semantics :
    ((Generated.hostChunk075[2]).induced.toList, (Generated.hostChunk075[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[2]).mask)) := by
  have hm : (Generated.hostChunk075[2]).mask = 122682 := by decide +kernel
  have hv : ((Generated.hostChunk075[2]).induced.toList, (Generated.hostChunk075[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 5, 1, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0902]

theorem fixed_values_0903 :
    (fixedDensityCounts (maskGraph 7 122683), fixedComplementCounts (maskGraph 7 122683)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 1, 0, 0, 0, 3, 0, 0, 1, 4, 4, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 3, 2, 2, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0903_semantics :
    ((Generated.hostChunk075[3]).induced.toList, (Generated.hostChunk075[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[3]).mask)) := by
  have hm : (Generated.hostChunk075[3]).mask = 122683 := by decide +kernel
  have hv : ((Generated.hostChunk075[3]).induced.toList, (Generated.hostChunk075[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0, 1, 0, 0, 0, 3, 0, 0, 1, 4, 4, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 3, 2, 2, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0903]

theorem fixed_values_0904 :
    (fixedDensityCounts (maskGraph 7 122686), fixedComplementCounts (maskGraph 7 122686)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 2, 1, 0, 1, 6, 1, 2, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0904_semantics :
    ((Generated.hostChunk075[4]).induced.toList, (Generated.hostChunk075[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[4]).mask)) := by
  have hm : (Generated.hostChunk075[4]).mask = 122686 := by decide +kernel
  have hv : ((Generated.hostChunk075[4]).induced.toList, (Generated.hostChunk075[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 2, 1, 0, 1, 6, 1, 2, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0904]

theorem fixed_values_0905 :
    (fixedDensityCounts (maskGraph 7 122687), fixedComplementCounts (maskGraph 7 122687)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 7, 0, 3, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 2, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0905_semantics :
    ((Generated.hostChunk075[5]).induced.toList, (Generated.hostChunk075[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[5]).mask)) := by
  have hm : (Generated.hostChunk075[5]).mask = 122687 := by decide +kernel
  have hv : ((Generated.hostChunk075[5]).induced.toList, (Generated.hostChunk075[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 7, 0, 3, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 2, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0905]

theorem fixed_values_0906 :
    (fixedDensityCounts (maskGraph 7 122746), fixedComplementCounts (maskGraph 7 122746)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0906_semantics :
    ((Generated.hostChunk075[6]).induced.toList, (Generated.hostChunk075[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[6]).mask)) := by
  have hm : (Generated.hostChunk075[6]).mask = 122746 := by decide +kernel
  have hv : ((Generated.hostChunk075[6]).induced.toList, (Generated.hostChunk075[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0906]

theorem fixed_values_0907 :
    (fixedDensityCounts (maskGraph 7 122747), fixedComplementCounts (maskGraph 7 122747)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2, 2, 4, 3, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 2, 3, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0907_semantics :
    ((Generated.hostChunk075[7]).induced.toList, (Generated.hostChunk075[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[7]).mask)) := by
  have hm : (Generated.hostChunk075[7]).mask = 122747 := by decide +kernel
  have hv : ((Generated.hostChunk075[7]).induced.toList, (Generated.hostChunk075[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2, 2, 4, 3, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 2, 3, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0907]

theorem fixed_values_0908 :
    (fixedDensityCounts (maskGraph 7 122748), fixedComplementCounts (maskGraph 7 122748)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 8, 3, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0908_semantics :
    ((Generated.hostChunk075[8]).induced.toList, (Generated.hostChunk075[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[8]).mask)) := by
  have hm : (Generated.hostChunk075[8]).mask = 122748 := by decide +kernel
  have hv : ((Generated.hostChunk075[8]).induced.toList, (Generated.hostChunk075[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 8, 3, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0908]

theorem fixed_values_0909 :
    (fixedDensityCounts (maskGraph 7 122749), fixedComplementCounts (maskGraph 7 122749)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 6, 4, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 4, 2, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0909_semantics :
    ((Generated.hostChunk075[9]).induced.toList, (Generated.hostChunk075[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[9]).mask)) := by
  have hm : (Generated.hostChunk075[9]).mask = 122749 := by decide +kernel
  have hv : ((Generated.hostChunk075[9]).induced.toList, (Generated.hostChunk075[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 6, 4, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 4, 2, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0909]

theorem fixed_values_0910 :
    (fixedDensityCounts (maskGraph 7 122750), fixedComplementCounts (maskGraph 7 122750)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 5, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0910_semantics :
    ((Generated.hostChunk075[10]).induced.toList, (Generated.hostChunk075[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[10]).mask)) := by
  have hm : (Generated.hostChunk075[10]).mask = 122750 := by decide +kernel
  have hv : ((Generated.hostChunk075[10]).induced.toList, (Generated.hostChunk075[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 5, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0910]

theorem fixed_values_0911 :
    (fixedDensityCounts (maskGraph 7 122751), fixedComplementCounts (maskGraph 7 122751)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 5, 2, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 3, 1, 1, 0]) := by
  decide +kernel

theorem fixed_host_0911_semantics :
    ((Generated.hostChunk075[11]).induced.toList, (Generated.hostChunk075[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk075[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk075[11]).mask)) := by
  have hm : (Generated.hostChunk075[11]).mask = 122751 := by decide +kernel
  have hv : ((Generated.hostChunk075[11]).induced.toList, (Generated.hostChunk075[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 5, 2, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 3, 1, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0911]

theorem fixed_chunk_075_semantics :
    ∀ h ∈ Generated.hostChunk075.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk075.toList = [Generated.hostChunk075[0], Generated.hostChunk075[1], Generated.hostChunk075[2], Generated.hostChunk075[3], Generated.hostChunk075[4], Generated.hostChunk075[5], Generated.hostChunk075[6], Generated.hostChunk075[7], Generated.hostChunk075[8], Generated.hostChunk075[9], Generated.hostChunk075[10], Generated.hostChunk075[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0900_semantics
  · exact fixed_host_0901_semantics
  · exact fixed_host_0902_semantics
  · exact fixed_host_0903_semantics
  · exact fixed_host_0904_semantics
  · exact fixed_host_0905_semantics
  · exact fixed_host_0906_semantics
  · exact fixed_host_0907_semantics
  · exact fixed_host_0908_semantics
  · exact fixed_host_0909_semantics
  · exact fixed_host_0910_semantics
  · exact fixed_host_0911_semantics

end InducedPentagons.Paper

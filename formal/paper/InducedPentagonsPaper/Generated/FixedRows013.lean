import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData013
import InducedPentagonsPaper.Generated.FixedRows005

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0156 :
    (fixedDensityCounts (maskGraph 7 2927), fixedComplementCounts (maskGraph 7 2927)) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0156_semantics :
    ((Generated.hostChunk013[0]).induced.toList, (Generated.hostChunk013[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[0]).mask)) := by
  have hm : (Generated.hostChunk013[0]).mask = 2927 := by decide +kernel
  have hv : ((Generated.hostChunk013[0]).induced.toList, (Generated.hostChunk013[0]).complement.toList) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0156]

theorem fixed_values_0157 :
    (fixedDensityCounts (maskGraph 7 2936), fixedComplementCounts (maskGraph 7 2936)) =
      ([0, 1, 1, 3, 0, 0, 0, 4, 0, 4, 1, 0, 1, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0157_semantics :
    ((Generated.hostChunk013[1]).induced.toList, (Generated.hostChunk013[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[1]).mask)) := by
  have hm : (Generated.hostChunk013[1]).mask = 2936 := by decide +kernel
  have hv : ((Generated.hostChunk013[1]).induced.toList, (Generated.hostChunk013[1]).complement.toList) =
      ([0, 1, 1, 3, 0, 0, 0, 4, 0, 4, 1, 0, 1, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0157]

theorem fixed_values_0158 :
    (fixedDensityCounts (maskGraph 7 2937), fixedComplementCounts (maskGraph 7 2937)) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 2, 3, 1, 0, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0158_semantics :
    ((Generated.hostChunk013[2]).induced.toList, (Generated.hostChunk013[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[2]).mask)) := by
  have hm : (Generated.hostChunk013[2]).mask = 2937 := by decide +kernel
  have hv : ((Generated.hostChunk013[2]).induced.toList, (Generated.hostChunk013[2]).complement.toList) =
      ([0, 1, 1, 3, 0, 0, 0, 2, 2, 3, 1, 0, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0158]

theorem fixed_values_0159 :
    (fixedDensityCounts (maskGraph 7 2938), fixedComplementCounts (maskGraph 7 2938)) =
      ([0, 1, 1, 2, 1, 0, 0, 4, 0, 0, 5, 0, 1, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0159_semantics :
    ((Generated.hostChunk013[3]).induced.toList, (Generated.hostChunk013[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[3]).mask)) := by
  have hm : (Generated.hostChunk013[3]).mask = 2938 := by decide +kernel
  have hv : ((Generated.hostChunk013[3]).induced.toList, (Generated.hostChunk013[3]).complement.toList) =
      ([0, 1, 1, 2, 1, 0, 0, 4, 0, 0, 5, 0, 1, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0159]

theorem fixed_values_0160 :
    (fixedDensityCounts (maskGraph 7 2939), fixedComplementCounts (maskGraph 7 2939)) =
      ([0, 1, 1, 2, 1, 0, 0, 2, 2, 0, 4, 0, 0, 1, 0, 1, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0160_semantics :
    ((Generated.hostChunk013[4]).induced.toList, (Generated.hostChunk013[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[4]).mask)) := by
  have hm : (Generated.hostChunk013[4]).mask = 2939 := by decide +kernel
  have hv : ((Generated.hostChunk013[4]).induced.toList, (Generated.hostChunk013[4]).complement.toList) =
      ([0, 1, 1, 2, 1, 0, 0, 2, 2, 0, 4, 0, 0, 1, 0, 1, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0160]

theorem fixed_values_0161 :
    (fixedDensityCounts (maskGraph 7 2940), fixedComplementCounts (maskGraph 7 2940)) =
      ([0, 1, 1, 2, 1, 0, 0, 2, 0, 0, 6, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0161_semantics :
    ((Generated.hostChunk013[5]).induced.toList, (Generated.hostChunk013[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[5]).mask)) := by
  have hm : (Generated.hostChunk013[5]).mask = 2940 := by decide +kernel
  have hv : ((Generated.hostChunk013[5]).induced.toList, (Generated.hostChunk013[5]).complement.toList) =
      ([0, 1, 1, 2, 1, 0, 0, 2, 0, 0, 6, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0161]

theorem fixed_values_0162 :
    (fixedDensityCounts (maskGraph 7 2941), fixedComplementCounts (maskGraph 7 2941)) =
      ([0, 1, 1, 2, 1, 0, 0, 2, 0, 0, 4, 2, 0, 0, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0162_semantics :
    ((Generated.hostChunk013[6]).induced.toList, (Generated.hostChunk013[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[6]).mask)) := by
  have hm : (Generated.hostChunk013[6]).mask = 2941 := by decide +kernel
  have hv : ((Generated.hostChunk013[6]).induced.toList, (Generated.hostChunk013[6]).complement.toList) =
      ([0, 1, 1, 2, 1, 0, 0, 2, 0, 0, 4, 2, 0, 0, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0162]

theorem fixed_values_0163 :
    (fixedDensityCounts (maskGraph 7 2942), fixedComplementCounts (maskGraph 7 2942)) =
      ([0, 1, 1, 1, 2, 0, 0, 2, 0, 0, 3, 3, 0, 0, 0, 1, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0163_semantics :
    ((Generated.hostChunk013[7]).induced.toList, (Generated.hostChunk013[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[7]).mask)) := by
  have hm : (Generated.hostChunk013[7]).mask = 2942 := by decide +kernel
  have hv : ((Generated.hostChunk013[7]).induced.toList, (Generated.hostChunk013[7]).complement.toList) =
      ([0, 1, 1, 1, 2, 0, 0, 2, 0, 0, 3, 3, 0, 0, 0, 1, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0163]

theorem fixed_values_0164 :
    (fixedDensityCounts (maskGraph 7 2943), fixedComplementCounts (maskGraph 7 2943)) =
      ([0, 1, 1, 1, 2, 0, 0, 2, 0, 0, 1, 5, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0164_semantics :
    ((Generated.hostChunk013[8]).induced.toList, (Generated.hostChunk013[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[8]).mask)) := by
  have hm : (Generated.hostChunk013[8]).mask = 2943 := by decide +kernel
  have hv : ((Generated.hostChunk013[8]).induced.toList, (Generated.hostChunk013[8]).complement.toList) =
      ([0, 1, 1, 1, 2, 0, 0, 2, 0, 0, 1, 5, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0164]

theorem fixed_values_0165 :
    (fixedDensityCounts (maskGraph 7 3038), fixedComplementCounts (maskGraph 7 3038)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 5, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0165_semantics :
    ((Generated.hostChunk013[9]).induced.toList, (Generated.hostChunk013[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[9]).mask)) := by
  have hm : (Generated.hostChunk013[9]).mask = 3038 := by decide +kernel
  have hv : ((Generated.hostChunk013[9]).induced.toList, (Generated.hostChunk013[9]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 5, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0165]

theorem fixed_values_0166 :
    (fixedDensityCounts (maskGraph 7 3039), fixedComplementCounts (maskGraph 7 3039)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 5, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0166_semantics :
    ((Generated.hostChunk013[10]).induced.toList, (Generated.hostChunk013[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[10]).mask)) := by
  have hm : (Generated.hostChunk013[10]).mask = 3039 := by decide +kernel
  have hv : ((Generated.hostChunk013[10]).induced.toList, (Generated.hostChunk013[10]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 5, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0166]

theorem fixed_values_0167 :
    (fixedDensityCounts (maskGraph 7 3054), fixedComplementCounts (maskGraph 7 3054)) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0167_semantics :
    ((Generated.hostChunk013[11]).induced.toList, (Generated.hostChunk013[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk013[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk013[11]).mask)) := by
  have hm : (Generated.hostChunk013[11]).mask = 3054 := by decide +kernel
  have hv : ((Generated.hostChunk013[11]).induced.toList, (Generated.hostChunk013[11]).complement.toList) =
      ([0, 1, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0167]

theorem fixed_chunk_013_semantics :
    ∀ h ∈ Generated.hostChunk013.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk013.toList = [Generated.hostChunk013[0], Generated.hostChunk013[1], Generated.hostChunk013[2], Generated.hostChunk013[3], Generated.hostChunk013[4], Generated.hostChunk013[5], Generated.hostChunk013[6], Generated.hostChunk013[7], Generated.hostChunk013[8], Generated.hostChunk013[9], Generated.hostChunk013[10], Generated.hostChunk013[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0156_semantics
  · exact fixed_host_0157_semantics
  · exact fixed_host_0158_semantics
  · exact fixed_host_0159_semantics
  · exact fixed_host_0160_semantics
  · exact fixed_host_0161_semantics
  · exact fixed_host_0162_semantics
  · exact fixed_host_0163_semantics
  · exact fixed_host_0164_semantics
  · exact fixed_host_0165_semantics
  · exact fixed_host_0166_semantics
  · exact fixed_host_0167_semantics

end InducedPentagons.Paper

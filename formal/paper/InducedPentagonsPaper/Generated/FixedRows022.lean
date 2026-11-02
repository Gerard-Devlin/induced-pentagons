import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData022
import InducedPentagonsPaper.Generated.FixedRows014

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0264 :
    (fixedDensityCounts (maskGraph 7 7089), fixedComplementCounts (maskGraph 7 7089)) =
      ([0, 0, 2, 1, 0, 0, 0, 2, 1, 4, 1, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0264_semantics :
    ((Generated.hostChunk022[0]).induced.toList, (Generated.hostChunk022[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[0]).mask)) := by
  have hm : (Generated.hostChunk022[0]).mask = 7089 := by decide +kernel
  have hv : ((Generated.hostChunk022[0]).induced.toList, (Generated.hostChunk022[0]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 2, 1, 4, 1, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0264]

theorem fixed_values_0265 :
    (fixedDensityCounts (maskGraph 7 7090), fixedComplementCounts (maskGraph 7 7090)) =
      ([0, 0, 2, 1, 0, 0, 0, 2, 0, 1, 6, 0, 1, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0265_semantics :
    ((Generated.hostChunk022[1]).induced.toList, (Generated.hostChunk022[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[1]).mask)) := by
  have hm : (Generated.hostChunk022[1]).mask = 7090 := by decide +kernel
  have hv : ((Generated.hostChunk022[1]).induced.toList, (Generated.hostChunk022[1]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 2, 0, 1, 6, 0, 1, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0265]

theorem fixed_values_0266 :
    (fixedDensityCounts (maskGraph 7 7091), fixedComplementCounts (maskGraph 7 7091)) =
      ([0, 0, 2, 1, 0, 0, 0, 2, 0, 0, 5, 2, 1, 0, 0, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0266_semantics :
    ((Generated.hostChunk022[2]).induced.toList, (Generated.hostChunk022[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[2]).mask)) := by
  have hm : (Generated.hostChunk022[2]).mask = 7091 := by decide +kernel
  have hv : ((Generated.hostChunk022[2]).induced.toList, (Generated.hostChunk022[2]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 2, 0, 0, 5, 2, 1, 0, 0, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0266]

theorem fixed_values_0267 :
    (fixedDensityCounts (maskGraph 7 7092), fixedComplementCounts (maskGraph 7 7092)) =
      ([0, 0, 1, 2, 0, 0, 0, 3, 0, 2, 2, 0, 1, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0267_semantics :
    ((Generated.hostChunk022[3]).induced.toList, (Generated.hostChunk022[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[3]).mask)) := by
  have hm : (Generated.hostChunk022[3]).mask = 7092 := by decide +kernel
  have hv : ((Generated.hostChunk022[3]).induced.toList, (Generated.hostChunk022[3]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 3, 0, 2, 2, 0, 1, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0267]

theorem fixed_values_0268 :
    (fixedDensityCounts (maskGraph 7 7093), fixedComplementCounts (maskGraph 7 7093)) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 1, 1, 1, 0, 1, 0, 3, 3, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0268_semantics :
    ((Generated.hostChunk022[4]).induced.toList, (Generated.hostChunk022[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[4]).mask)) := by
  have hm : (Generated.hostChunk022[4]).mask = 7093 := by decide +kernel
  have hv : ((Generated.hostChunk022[4]).induced.toList, (Generated.hostChunk022[4]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 1, 1, 1, 0, 1, 0, 3, 3, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0268]

theorem fixed_values_0269 :
    (fixedDensityCounts (maskGraph 7 7094), fixedComplementCounts (maskGraph 7 7094)) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0269_semantics :
    ((Generated.hostChunk022[5]).induced.toList, (Generated.hostChunk022[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[5]).mask)) := by
  have hm : (Generated.hostChunk022[5]).mask = 7094 := by decide +kernel
  have hv : ((Generated.hostChunk022[5]).induced.toList, (Generated.hostChunk022[5]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0269]

theorem fixed_values_0270 :
    (fixedDensityCounts (maskGraph 7 7095), fixedComplementCounts (maskGraph 7 7095)) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 4, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0270_semantics :
    ((Generated.hostChunk022[6]).induced.toList, (Generated.hostChunk022[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[6]).mask)) := by
  have hm : (Generated.hostChunk022[6]).mask = 7095 := by decide +kernel
  have hv : ((Generated.hostChunk022[6]).induced.toList, (Generated.hostChunk022[6]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 4, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0270]

theorem fixed_values_0271 :
    (fixedDensityCounts (maskGraph 7 7100), fixedComplementCounts (maskGraph 7 7100)) =
      ([0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 4, 0, 1, 0, 0, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0271_semantics :
    ((Generated.hostChunk022[7]).induced.toList, (Generated.hostChunk022[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[7]).mask)) := by
  have hm : (Generated.hostChunk022[7]).mask = 7100 := by decide +kernel
  have hv : ((Generated.hostChunk022[7]).induced.toList, (Generated.hostChunk022[7]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 4, 0, 1, 0, 0, 0, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0271]

theorem fixed_values_0272 :
    (fixedDensityCounts (maskGraph 7 7101), fixedComplementCounts (maskGraph 7 7101)) =
      ([0, 0, 1, 1, 1, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 2, 3, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0272_semantics :
    ((Generated.hostChunk022[8]).induced.toList, (Generated.hostChunk022[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[8]).mask)) := by
  have hm : (Generated.hostChunk022[8]).mask = 7101 := by decide +kernel
  have hv : ((Generated.hostChunk022[8]).induced.toList, (Generated.hostChunk022[8]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 2, 3, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0272]

theorem fixed_values_0273 :
    (fixedDensityCounts (maskGraph 7 7102), fixedComplementCounts (maskGraph 7 7102)) =
      ([0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 2, 4, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0273_semantics :
    ((Generated.hostChunk022[9]).induced.toList, (Generated.hostChunk022[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[9]).mask)) := by
  have hm : (Generated.hostChunk022[9]).mask = 7102 := by decide +kernel
  have hv : ((Generated.hostChunk022[9]).induced.toList, (Generated.hostChunk022[9]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 1, 2, 1, 0, 0, 2, 4, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0273]

theorem fixed_values_0274 :
    (fixedDensityCounts (maskGraph 7 7103), fixedComplementCounts (maskGraph 7 7103)) =
      ([0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0, 0, 1, 7, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0274_semantics :
    ((Generated.hostChunk022[10]).induced.toList, (Generated.hostChunk022[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[10]).mask)) := by
  have hm : (Generated.hostChunk022[10]).mask = 7103 := by decide +kernel
  have hv : ((Generated.hostChunk022[10]).induced.toList, (Generated.hostChunk022[10]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0, 0, 1, 7, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0274]

theorem fixed_values_0275 :
    (fixedDensityCounts (maskGraph 7 7134), fixedComplementCounts (maskGraph 7 7134)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0275_semantics :
    ((Generated.hostChunk022[11]).induced.toList, (Generated.hostChunk022[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk022[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk022[11]).mask)) := by
  have hm : (Generated.hostChunk022[11]).mask = 7134 := by decide +kernel
  have hv : ((Generated.hostChunk022[11]).induced.toList, (Generated.hostChunk022[11]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0275]

theorem fixed_chunk_022_semantics :
    ∀ h ∈ Generated.hostChunk022.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk022.toList = [Generated.hostChunk022[0], Generated.hostChunk022[1], Generated.hostChunk022[2], Generated.hostChunk022[3], Generated.hostChunk022[4], Generated.hostChunk022[5], Generated.hostChunk022[6], Generated.hostChunk022[7], Generated.hostChunk022[8], Generated.hostChunk022[9], Generated.hostChunk022[10], Generated.hostChunk022[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0264_semantics
  · exact fixed_host_0265_semantics
  · exact fixed_host_0266_semantics
  · exact fixed_host_0267_semantics
  · exact fixed_host_0268_semantics
  · exact fixed_host_0269_semantics
  · exact fixed_host_0270_semantics
  · exact fixed_host_0271_semantics
  · exact fixed_host_0272_semantics
  · exact fixed_host_0273_semantics
  · exact fixed_host_0274_semantics
  · exact fixed_host_0275_semantics

end InducedPentagons.Paper

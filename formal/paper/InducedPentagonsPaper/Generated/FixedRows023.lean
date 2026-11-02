import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData023
import InducedPentagonsPaper.Generated.FixedRows015

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0276 :
    (fixedDensityCounts (maskGraph 7 7135), fixedComplementCounts (maskGraph 7 7135)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0276_semantics :
    ((Generated.hostChunk023[0]).induced.toList, (Generated.hostChunk023[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[0]).mask)) := by
  have hm : (Generated.hostChunk023[0]).mask = 7135 := by decide +kernel
  have hv : ((Generated.hostChunk023[0]).induced.toList, (Generated.hostChunk023[0]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0276]

theorem fixed_values_0277 :
    (fixedDensityCounts (maskGraph 7 7150), fixedComplementCounts (maskGraph 7 7150)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 3, 0, 2, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0277_semantics :
    ((Generated.hostChunk023[1]).induced.toList, (Generated.hostChunk023[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[1]).mask)) := by
  have hm : (Generated.hostChunk023[1]).mask = 7150 := by decide +kernel
  have hv : ((Generated.hostChunk023[1]).induced.toList, (Generated.hostChunk023[1]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 3, 0, 2, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0277]

theorem fixed_values_0278 :
    (fixedDensityCounts (maskGraph 7 7151), fixedComplementCounts (maskGraph 7 7151)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0278_semantics :
    ((Generated.hostChunk023[2]).induced.toList, (Generated.hostChunk023[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[2]).mask)) := by
  have hm : (Generated.hostChunk023[2]).mask = 7151 := by decide +kernel
  have hv : ((Generated.hostChunk023[2]).induced.toList, (Generated.hostChunk023[2]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0278]

theorem fixed_values_0279 :
    (fixedDensityCounts (maskGraph 7 7152), fixedComplementCounts (maskGraph 7 7152)) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 5, 1, 0, 0, 2, 3, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0279_semantics :
    ((Generated.hostChunk023[3]).induced.toList, (Generated.hostChunk023[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[3]).mask)) := by
  have hm : (Generated.hostChunk023[3]).mask = 7152 := by decide +kernel
  have hv : ((Generated.hostChunk023[3]).induced.toList, (Generated.hostChunk023[3]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 5, 1, 0, 0, 2, 3, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0279]

theorem fixed_values_0280 :
    (fixedDensityCounts (maskGraph 7 7153), fixedComplementCounts (maskGraph 7 7153)) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0280_semantics :
    ((Generated.hostChunk023[4]).induced.toList, (Generated.hostChunk023[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[4]).mask)) := by
  have hm : (Generated.hostChunk023[4]).mask = 7153 := by decide +kernel
  have hv : ((Generated.hostChunk023[4]).induced.toList, (Generated.hostChunk023[4]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0280]

theorem fixed_values_0281 :
    (fixedDensityCounts (maskGraph 7 7154), fixedComplementCounts (maskGraph 7 7154)) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 1, 5, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0281_semantics :
    ((Generated.hostChunk023[5]).induced.toList, (Generated.hostChunk023[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[5]).mask)) := by
  have hm : (Generated.hostChunk023[5]).mask = 7154 := by decide +kernel
  have hv : ((Generated.hostChunk023[5]).induced.toList, (Generated.hostChunk023[5]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 1, 5, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0281]

theorem fixed_values_0282 :
    (fixedDensityCounts (maskGraph 7 7155), fixedComplementCounts (maskGraph 7 7155)) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 5, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0282_semantics :
    ((Generated.hostChunk023[6]).induced.toList, (Generated.hostChunk023[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[6]).mask)) := by
  have hm : (Generated.hostChunk023[6]).mask = 7155 := by decide +kernel
  have hv : ((Generated.hostChunk023[6]).induced.toList, (Generated.hostChunk023[6]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 5, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0282]

theorem fixed_values_0283 :
    (fixedDensityCounts (maskGraph 7 7156), fixedComplementCounts (maskGraph 7 7156)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 1, 0, 0, 1, 5, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0283_semantics :
    ((Generated.hostChunk023[7]).induced.toList, (Generated.hostChunk023[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[7]).mask)) := by
  have hm : (Generated.hostChunk023[7]).mask = 7156 := by decide +kernel
  have hv : ((Generated.hostChunk023[7]).induced.toList, (Generated.hostChunk023[7]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 1, 0, 0, 1, 5, 0, 2, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0283]

theorem fixed_values_0284 :
    (fixedDensityCounts (maskGraph 7 7157), fixedComplementCounts (maskGraph 7 7157)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 1, 0, 0, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0284_semantics :
    ((Generated.hostChunk023[8]).induced.toList, (Generated.hostChunk023[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[8]).mask)) := by
  have hm : (Generated.hostChunk023[8]).mask = 7157 := by decide +kernel
  have hv : ((Generated.hostChunk023[8]).induced.toList, (Generated.hostChunk023[8]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 1, 0, 0, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0284]

theorem fixed_values_0285 :
    (fixedDensityCounts (maskGraph 7 7158), fixedComplementCounts (maskGraph 7 7158)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 1, 2, 2, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0285_semantics :
    ((Generated.hostChunk023[9]).induced.toList, (Generated.hostChunk023[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[9]).mask)) := by
  have hm : (Generated.hostChunk023[9]).mask = 7158 := by decide +kernel
  have hv : ((Generated.hostChunk023[9]).induced.toList, (Generated.hostChunk023[9]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 1, 2, 2, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0285]

theorem fixed_values_0286 :
    (fixedDensityCounts (maskGraph 7 7159), fixedComplementCounts (maskGraph 7 7159)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 1, 0, 4, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0286_semantics :
    ((Generated.hostChunk023[10]).induced.toList, (Generated.hostChunk023[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[10]).mask)) := by
  have hm : (Generated.hostChunk023[10]).mask = 7159 := by decide +kernel
  have hv : ((Generated.hostChunk023[10]).induced.toList, (Generated.hostChunk023[10]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 1, 0, 1, 0, 4, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0286]

theorem fixed_values_0287 :
    (fixedDensityCounts (maskGraph 7 7164), fixedComplementCounts (maskGraph 7 7164)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0, 5, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0287_semantics :
    ((Generated.hostChunk023[11]).induced.toList, (Generated.hostChunk023[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk023[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk023[11]).mask)) := by
  have hm : (Generated.hostChunk023[11]).mask = 7164 := by decide +kernel
  have hv : ((Generated.hostChunk023[11]).induced.toList, (Generated.hostChunk023[11]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0, 5, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0287]

theorem fixed_chunk_023_semantics :
    ∀ h ∈ Generated.hostChunk023.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk023.toList = [Generated.hostChunk023[0], Generated.hostChunk023[1], Generated.hostChunk023[2], Generated.hostChunk023[3], Generated.hostChunk023[4], Generated.hostChunk023[5], Generated.hostChunk023[6], Generated.hostChunk023[7], Generated.hostChunk023[8], Generated.hostChunk023[9], Generated.hostChunk023[10], Generated.hostChunk023[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0276_semantics
  · exact fixed_host_0277_semantics
  · exact fixed_host_0278_semantics
  · exact fixed_host_0279_semantics
  · exact fixed_host_0280_semantics
  · exact fixed_host_0281_semantics
  · exact fixed_host_0282_semantics
  · exact fixed_host_0283_semantics
  · exact fixed_host_0284_semantics
  · exact fixed_host_0285_semantics
  · exact fixed_host_0286_semantics
  · exact fixed_host_0287_semantics

end InducedPentagons.Paper

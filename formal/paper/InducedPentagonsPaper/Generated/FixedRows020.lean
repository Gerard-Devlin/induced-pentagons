import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData020
import InducedPentagonsPaper.Generated.FixedRows012

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0240 :
    (fixedDensityCounts (maskGraph 7 6877), fixedComplementCounts (maskGraph 7 6877)) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 5, 0, 0, 0, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 3, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0240_semantics :
    ((Generated.hostChunk020[0]).induced.toList, (Generated.hostChunk020[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[0]).mask)) := by
  have hm : (Generated.hostChunk020[0]).mask = 6877 := by decide +kernel
  have hv : ((Generated.hostChunk020[0]).induced.toList, (Generated.hostChunk020[0]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 5, 0, 0, 0, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 3, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0240]

theorem fixed_values_0241 :
    (fixedDensityCounts (maskGraph 7 6879), fixedComplementCounts (maskGraph 7 6879)) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 6, 0, 0, 0, 0, 4, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 1, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0241_semantics :
    ((Generated.hostChunk020[1]).induced.toList, (Generated.hostChunk020[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[1]).mask)) := by
  have hm : (Generated.hostChunk020[1]).mask = 6879 := by decide +kernel
  have hv : ((Generated.hostChunk020[1]).induced.toList, (Generated.hostChunk020[1]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 6, 0, 0, 0, 0, 4, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 1, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0241]

theorem fixed_values_0242 :
    (fixedDensityCounts (maskGraph 7 6887), fixedComplementCounts (maskGraph 7 6887)) =
      ([0, 0, 3, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0242_semantics :
    ((Generated.hostChunk020[2]).induced.toList, (Generated.hostChunk020[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[2]).mask)) := by
  have hm : (Generated.hostChunk020[2]).mask = 6887 := by decide +kernel
  have hv : ((Generated.hostChunk020[2]).induced.toList, (Generated.hostChunk020[2]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0242]

theorem fixed_values_0243 :
    (fixedDensityCounts (maskGraph 7 6890), fixedComplementCounts (maskGraph 7 6890)) =
      ([0, 0, 3, 0, 0, 0, 0, 2, 4, 4, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0243_semantics :
    ((Generated.hostChunk020[3]).induced.toList, (Generated.hostChunk020[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[3]).mask)) := by
  have hm : (Generated.hostChunk020[3]).mask = 6890 := by decide +kernel
  have hv : ((Generated.hostChunk020[3]).induced.toList, (Generated.hostChunk020[3]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 0, 2, 4, 4, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0243]

theorem fixed_values_0244 :
    (fixedDensityCounts (maskGraph 7 6891), fixedComplementCounts (maskGraph 7 6891)) =
      ([0, 0, 3, 0, 0, 0, 0, 2, 4, 0, 4, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0244_semantics :
    ((Generated.hostChunk020[4]).induced.toList, (Generated.hostChunk020[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[4]).mask)) := by
  have hm : (Generated.hostChunk020[4]).mask = 6891 := by decide +kernel
  have hv : ((Generated.hostChunk020[4]).induced.toList, (Generated.hostChunk020[4]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 0, 2, 4, 0, 4, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0244]

theorem fixed_values_0245 :
    (fixedDensityCounts (maskGraph 7 6892), fixedComplementCounts (maskGraph 7 6892)) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 2, 2, 1, 0, 1, 0, 4, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0245_semantics :
    ((Generated.hostChunk020[5]).induced.toList, (Generated.hostChunk020[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[5]).mask)) := by
  have hm : (Generated.hostChunk020[5]).mask = 6892 := by decide +kernel
  have hv : ((Generated.hostChunk020[5]).induced.toList, (Generated.hostChunk020[5]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 2, 2, 1, 0, 1, 0, 4, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0245]

theorem fixed_values_0246 :
    (fixedDensityCounts (maskGraph 7 6893), fixedComplementCounts (maskGraph 7 6893)) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 2, 0, 2, 1, 1, 0, 0, 3, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0246_semantics :
    ((Generated.hostChunk020[6]).induced.toList, (Generated.hostChunk020[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[6]).mask)) := by
  have hm : (Generated.hostChunk020[6]).mask = 6893 := by decide +kernel
  have hv : ((Generated.hostChunk020[6]).induced.toList, (Generated.hostChunk020[6]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 2, 0, 2, 1, 1, 0, 0, 3, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0246]

theorem fixed_values_0247 :
    (fixedDensityCounts (maskGraph 7 6894), fixedComplementCounts (maskGraph 7 6894)) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 4, 1, 1, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0247_semantics :
    ((Generated.hostChunk020[7]).induced.toList, (Generated.hostChunk020[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[7]).mask)) := by
  have hm : (Generated.hostChunk020[7]).mask = 6894 := by decide +kernel
  have hv : ((Generated.hostChunk020[7]).induced.toList, (Generated.hostChunk020[7]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 4, 1, 1, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0247]

theorem fixed_values_0248 :
    (fixedDensityCounts (maskGraph 7 6895), fixedComplementCounts (maskGraph 7 6895)) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 4, 0, 1, 1, 0, 1, 0, 4, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0248_semantics :
    ((Generated.hostChunk020[8]).induced.toList, (Generated.hostChunk020[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[8]).mask)) := by
  have hm : (Generated.hostChunk020[8]).mask = 6895 := by decide +kernel
  have hv : ((Generated.hostChunk020[8]).induced.toList, (Generated.hostChunk020[8]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 4, 0, 1, 1, 0, 1, 0, 4, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0248]

theorem fixed_values_0249 :
    (fixedDensityCounts (maskGraph 7 6904), fixedComplementCounts (maskGraph 7 6904)) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0249_semantics :
    ((Generated.hostChunk020[9]).induced.toList, (Generated.hostChunk020[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[9]).mask)) := by
  have hm : (Generated.hostChunk020[9]).mask = 6904 := by decide +kernel
  have hv : ((Generated.hostChunk020[9]).induced.toList, (Generated.hostChunk020[9]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0249]

theorem fixed_values_0250 :
    (fixedDensityCounts (maskGraph 7 6905), fixedComplementCounts (maskGraph 7 6905)) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 2, 1, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0250_semantics :
    ((Generated.hostChunk020[10]).induced.toList, (Generated.hostChunk020[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[10]).mask)) := by
  have hm : (Generated.hostChunk020[10]).mask = 6905 := by decide +kernel
  have hv : ((Generated.hostChunk020[10]).induced.toList, (Generated.hostChunk020[10]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 2, 1, 2, 1, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0250]

theorem fixed_values_0251 :
    (fixedDensityCounts (maskGraph 7 6907), fixedComplementCounts (maskGraph 7 6907)) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 2, 2, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0251_semantics :
    ((Generated.hostChunk020[11]).induced.toList, (Generated.hostChunk020[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk020[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk020[11]).mask)) := by
  have hm : (Generated.hostChunk020[11]).mask = 6907 := by decide +kernel
  have hv : ((Generated.hostChunk020[11]).induced.toList, (Generated.hostChunk020[11]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 2, 2, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0251]

theorem fixed_chunk_020_semantics :
    ∀ h ∈ Generated.hostChunk020.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk020.toList = [Generated.hostChunk020[0], Generated.hostChunk020[1], Generated.hostChunk020[2], Generated.hostChunk020[3], Generated.hostChunk020[4], Generated.hostChunk020[5], Generated.hostChunk020[6], Generated.hostChunk020[7], Generated.hostChunk020[8], Generated.hostChunk020[9], Generated.hostChunk020[10], Generated.hostChunk020[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0240_semantics
  · exact fixed_host_0241_semantics
  · exact fixed_host_0242_semantics
  · exact fixed_host_0243_semantics
  · exact fixed_host_0244_semantics
  · exact fixed_host_0245_semantics
  · exact fixed_host_0246_semantics
  · exact fixed_host_0247_semantics
  · exact fixed_host_0248_semantics
  · exact fixed_host_0249_semantics
  · exact fixed_host_0250_semantics
  · exact fixed_host_0251_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData025
import InducedPentagonsPaper.Generated.FixedRows017

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0300 :
    (fixedDensityCounts (maskGraph 7 7863), fixedComplementCounts (maskGraph 7 7863)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 3, 2, 2, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0300_semantics :
    ((Generated.hostChunk025[0]).induced.toList, (Generated.hostChunk025[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[0]).mask)) := by
  have hm : (Generated.hostChunk025[0]).mask = 7863 := by decide +kernel
  have hv : ((Generated.hostChunk025[0]).induced.toList, (Generated.hostChunk025[0]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 3, 2, 2, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0300]

theorem fixed_values_0301 :
    (fixedDensityCounts (maskGraph 7 7864), fixedComplementCounts (maskGraph 7 7864)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 11, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0301_semantics :
    ((Generated.hostChunk025[1]).induced.toList, (Generated.hostChunk025[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[1]).mask)) := by
  have hm : (Generated.hostChunk025[1]).mask = 7864 := by decide +kernel
  have hv : ((Generated.hostChunk025[1]).induced.toList, (Generated.hostChunk025[1]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 11, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0301]

theorem fixed_values_0302 :
    (fixedDensityCounts (maskGraph 7 7865), fixedComplementCounts (maskGraph 7 7865)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 4, 2, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0302_semantics :
    ((Generated.hostChunk025[2]).induced.toList, (Generated.hostChunk025[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[2]).mask)) := by
  have hm : (Generated.hostChunk025[2]).mask = 7865 := by decide +kernel
  have hv : ((Generated.hostChunk025[2]).induced.toList, (Generated.hostChunk025[2]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 4, 2, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0302]

theorem fixed_values_0303 :
    (fixedDensityCounts (maskGraph 7 7866), fixedComplementCounts (maskGraph 7 7866)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 4, 2, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0303_semantics :
    ((Generated.hostChunk025[3]).induced.toList, (Generated.hostChunk025[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[3]).mask)) := by
  have hm : (Generated.hostChunk025[3]).mask = 7866 := by decide +kernel
  have hv : ((Generated.hostChunk025[3]).induced.toList, (Generated.hostChunk025[3]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 4, 2, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0303]

theorem fixed_values_0304 :
    (fixedDensityCounts (maskGraph 7 7867), fixedComplementCounts (maskGraph 7 7867)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0304_semantics :
    ((Generated.hostChunk025[4]).induced.toList, (Generated.hostChunk025[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[4]).mask)) := by
  have hm : (Generated.hostChunk025[4]).mask = 7867 := by decide +kernel
  have hv : ((Generated.hostChunk025[4]).induced.toList, (Generated.hostChunk025[4]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0304]

theorem fixed_values_0305 :
    (fixedDensityCounts (maskGraph 7 7868), fixedComplementCounts (maskGraph 7 7868)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 3, 0, 1, 0, 4, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0305_semantics :
    ((Generated.hostChunk025[5]).induced.toList, (Generated.hostChunk025[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[5]).mask)) := by
  have hm : (Generated.hostChunk025[5]).mask = 7868 := by decide +kernel
  have hv : ((Generated.hostChunk025[5]).induced.toList, (Generated.hostChunk025[5]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 3, 0, 1, 0, 4, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0305]

theorem fixed_values_0306 :
    (fixedDensityCounts (maskGraph 7 7869), fixedComplementCounts (maskGraph 7 7869)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 0, 2, 3, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0306_semantics :
    ((Generated.hostChunk025[6]).induced.toList, (Generated.hostChunk025[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[6]).mask)) := by
  have hm : (Generated.hostChunk025[6]).mask = 7869 := by decide +kernel
  have hv : ((Generated.hostChunk025[6]).induced.toList, (Generated.hostChunk025[6]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 3, 0, 0, 1, 2, 0, 2, 3, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0306]

theorem fixed_values_0307 :
    (fixedDensityCounts (maskGraph 7 7870), fixedComplementCounts (maskGraph 7 7870)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 4, 2, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0307_semantics :
    ((Generated.hostChunk025[7]).induced.toList, (Generated.hostChunk025[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[7]).mask)) := by
  have hm : (Generated.hostChunk025[7]).mask = 7870 := by decide +kernel
  have hv : ((Generated.hostChunk025[7]).induced.toList, (Generated.hostChunk025[7]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 4, 2, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0307]

theorem fixed_values_0308 :
    (fixedDensityCounts (maskGraph 7 7871), fixedComplementCounts (maskGraph 7 7871)) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0308_semantics :
    ((Generated.hostChunk025[8]).induced.toList, (Generated.hostChunk025[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[8]).mask)) := by
  have hm : (Generated.hostChunk025[8]).mask = 7871 := by decide +kernel
  have hv : ((Generated.hostChunk025[8]).induced.toList, (Generated.hostChunk025[8]).complement.toList) =
      ([0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0308]

theorem fixed_values_0309 :
    (fixedDensityCounts (maskGraph 7 7926), fixedComplementCounts (maskGraph 7 7926)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 4, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0309_semantics :
    ((Generated.hostChunk025[9]).induced.toList, (Generated.hostChunk025[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[9]).mask)) := by
  have hm : (Generated.hostChunk025[9]).mask = 7926 := by decide +kernel
  have hv : ((Generated.hostChunk025[9]).induced.toList, (Generated.hostChunk025[9]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 4, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0309]

theorem fixed_values_0310 :
    (fixedDensityCounts (maskGraph 7 7927), fixedComplementCounts (maskGraph 7 7927)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 3, 0, 4, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0310_semantics :
    ((Generated.hostChunk025[10]).induced.toList, (Generated.hostChunk025[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[10]).mask)) := by
  have hm : (Generated.hostChunk025[10]).mask = 7927 := by decide +kernel
  have hv : ((Generated.hostChunk025[10]).induced.toList, (Generated.hostChunk025[10]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 3, 0, 4, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0310]

theorem fixed_values_0311 :
    (fixedDensityCounts (maskGraph 7 7930), fixedComplementCounts (maskGraph 7 7930)) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 4, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0311_semantics :
    ((Generated.hostChunk025[11]).induced.toList, (Generated.hostChunk025[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk025[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk025[11]).mask)) := by
  have hm : (Generated.hostChunk025[11]).mask = 7930 := by decide +kernel
  have hv : ((Generated.hostChunk025[11]).induced.toList, (Generated.hostChunk025[11]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 4, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0311]

theorem fixed_chunk_025_semantics :
    ∀ h ∈ Generated.hostChunk025.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk025.toList = [Generated.hostChunk025[0], Generated.hostChunk025[1], Generated.hostChunk025[2], Generated.hostChunk025[3], Generated.hostChunk025[4], Generated.hostChunk025[5], Generated.hostChunk025[6], Generated.hostChunk025[7], Generated.hostChunk025[8], Generated.hostChunk025[9], Generated.hostChunk025[10], Generated.hostChunk025[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0300_semantics
  · exact fixed_host_0301_semantics
  · exact fixed_host_0302_semantics
  · exact fixed_host_0303_semantics
  · exact fixed_host_0304_semantics
  · exact fixed_host_0305_semantics
  · exact fixed_host_0306_semantics
  · exact fixed_host_0307_semantics
  · exact fixed_host_0308_semantics
  · exact fixed_host_0309_semantics
  · exact fixed_host_0310_semantics
  · exact fixed_host_0311_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData042
import InducedPentagonsPaper.Generated.FixedRows034

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0504 :
    (fixedDensityCounts (maskGraph 7 42223), fixedComplementCounts (maskGraph 7 42223)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 4, 1, 0, 2, 1, 1, 0, 1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0504_semantics :
    ((Generated.hostChunk042[0]).induced.toList, (Generated.hostChunk042[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[0]).mask)) := by
  have hm : (Generated.hostChunk042[0]).mask = 42223 := by decide +kernel
  have hv : ((Generated.hostChunk042[0]).induced.toList, (Generated.hostChunk042[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 4, 1, 0, 2, 1, 1, 0, 1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0504]

theorem fixed_values_0505 :
    (fixedDensityCounts (maskGraph 7 42232), fixedComplementCounts (maskGraph 7 42232)) =
      ([0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 6, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0505_semantics :
    ((Generated.hostChunk042[1]).induced.toList, (Generated.hostChunk042[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[1]).mask)) := by
  have hm : (Generated.hostChunk042[1]).mask = 42232 := by decide +kernel
  have hv : ((Generated.hostChunk042[1]).induced.toList, (Generated.hostChunk042[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 6, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0505]

theorem fixed_values_0506 :
    (fixedDensityCounts (maskGraph 7 42233), fixedComplementCounts (maskGraph 7 42233)) =
      ([0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 4, 2, 0, 0, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0506_semantics :
    ((Generated.hostChunk042[2]).induced.toList, (Generated.hostChunk042[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[2]).mask)) := by
  have hm : (Generated.hostChunk042[2]).mask = 42233 := by decide +kernel
  have hv : ((Generated.hostChunk042[2]).induced.toList, (Generated.hostChunk042[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 4, 2, 0, 0, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0506]

theorem fixed_values_0507 :
    (fixedDensityCounts (maskGraph 7 42234), fixedComplementCounts (maskGraph 7 42234)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 5, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0507_semantics :
    ((Generated.hostChunk042[3]).induced.toList, (Generated.hostChunk042[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[3]).mask)) := by
  have hm : (Generated.hostChunk042[3]).mask = 42234 := by decide +kernel
  have hv : ((Generated.hostChunk042[3]).induced.toList, (Generated.hostChunk042[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 5, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0507]

theorem fixed_values_0508 :
    (fixedDensityCounts (maskGraph 7 42235), fixedComplementCounts (maskGraph 7 42235)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 4, 2, 0, 0, 1, 1, 1, 3, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0508_semantics :
    ((Generated.hostChunk042[4]).induced.toList, (Generated.hostChunk042[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[4]).mask)) := by
  have hm : (Generated.hostChunk042[4]).mask = 42235 := by decide +kernel
  have hv : ((Generated.hostChunk042[4]).induced.toList, (Generated.hostChunk042[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 4, 2, 0, 0, 1, 1, 1, 3, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0508]

theorem fixed_values_0509 :
    (fixedDensityCounts (maskGraph 7 42238), fixedComplementCounts (maskGraph 7 42238)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 4, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0509_semantics :
    ((Generated.hostChunk042[5]).induced.toList, (Generated.hostChunk042[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[5]).mask)) := by
  have hm : (Generated.hostChunk042[5]).mask = 42238 := by decide +kernel
  have hv : ((Generated.hostChunk042[5]).induced.toList, (Generated.hostChunk042[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 4, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0509]

theorem fixed_values_0510 :
    (fixedDensityCounts (maskGraph 7 42239), fixedComplementCounts (maskGraph 7 42239)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 5, 0, 0, 1, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0510_semantics :
    ((Generated.hostChunk042[6]).induced.toList, (Generated.hostChunk042[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[6]).mask)) := by
  have hm : (Generated.hostChunk042[6]).mask = 42239 := by decide +kernel
  have hv : ((Generated.hostChunk042[6]).induced.toList, (Generated.hostChunk042[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 5, 0, 0, 1, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0510]

theorem fixed_values_0511 :
    (fixedDensityCounts (maskGraph 7 42412), fixedComplementCounts (maskGraph 7 42412)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 7, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0511_semantics :
    ((Generated.hostChunk042[7]).induced.toList, (Generated.hostChunk042[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[7]).mask)) := by
  have hm : (Generated.hostChunk042[7]).mask = 42412 := by decide +kernel
  have hv : ((Generated.hostChunk042[7]).induced.toList, (Generated.hostChunk042[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 7, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0511]

theorem fixed_values_0512 :
    (fixedDensityCounts (maskGraph 7 42413), fixedComplementCounts (maskGraph 7 42413)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0512_semantics :
    ((Generated.hostChunk042[8]).induced.toList, (Generated.hostChunk042[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[8]).mask)) := by
  have hm : (Generated.hostChunk042[8]).mask = 42413 := by decide +kernel
  have hv : ((Generated.hostChunk042[8]).induced.toList, (Generated.hostChunk042[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0512]

theorem fixed_values_0513 :
    (fixedDensityCounts (maskGraph 7 42414), fixedComplementCounts (maskGraph 7 42414)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 2, 1, 3, 0, 2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0513_semantics :
    ((Generated.hostChunk042[9]).induced.toList, (Generated.hostChunk042[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[9]).mask)) := by
  have hm : (Generated.hostChunk042[9]).mask = 42414 := by decide +kernel
  have hv : ((Generated.hostChunk042[9]).induced.toList, (Generated.hostChunk042[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 2, 1, 3, 0, 2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0513]

theorem fixed_values_0514 :
    (fixedDensityCounts (maskGraph 7 42415), fixedComplementCounts (maskGraph 7 42415)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 0, 2, 0, 0, 0, 2, 0, 0, 1, 1, 4, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0514_semantics :
    ((Generated.hostChunk042[10]).induced.toList, (Generated.hostChunk042[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[10]).mask)) := by
  have hm : (Generated.hostChunk042[10]).mask = 42415 := by decide +kernel
  have hv : ((Generated.hostChunk042[10]).induced.toList, (Generated.hostChunk042[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 0, 2, 0, 0, 0, 2, 0, 0, 1, 1, 4, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0514]

theorem fixed_values_0515 :
    (fixedDensityCounts (maskGraph 7 42418), fixedComplementCounts (maskGraph 7 42418)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0515_semantics :
    ((Generated.hostChunk042[11]).induced.toList, (Generated.hostChunk042[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk042[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk042[11]).mask)) := by
  have hm : (Generated.hostChunk042[11]).mask = 42418 := by decide +kernel
  have hv : ((Generated.hostChunk042[11]).induced.toList, (Generated.hostChunk042[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0515]

theorem fixed_chunk_042_semantics :
    ∀ h ∈ Generated.hostChunk042.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk042.toList = [Generated.hostChunk042[0], Generated.hostChunk042[1], Generated.hostChunk042[2], Generated.hostChunk042[3], Generated.hostChunk042[4], Generated.hostChunk042[5], Generated.hostChunk042[6], Generated.hostChunk042[7], Generated.hostChunk042[8], Generated.hostChunk042[9], Generated.hostChunk042[10], Generated.hostChunk042[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0504_semantics
  · exact fixed_host_0505_semantics
  · exact fixed_host_0506_semantics
  · exact fixed_host_0507_semantics
  · exact fixed_host_0508_semantics
  · exact fixed_host_0509_semantics
  · exact fixed_host_0510_semantics
  · exact fixed_host_0511_semantics
  · exact fixed_host_0512_semantics
  · exact fixed_host_0513_semantics
  · exact fixed_host_0514_semantics
  · exact fixed_host_0515_semantics

end InducedPentagons.Paper

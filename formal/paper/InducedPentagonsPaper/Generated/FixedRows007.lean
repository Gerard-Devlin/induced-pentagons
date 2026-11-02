import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData007

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0084 :
    (fixedDensityCounts (maskGraph 7 2380), fixedComplementCounts (maskGraph 7 2380)) =
      ([0, 5, 5, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0084_semantics :
    ((Generated.hostChunk007[0]).induced.toList, (Generated.hostChunk007[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[0]).mask)) := by
  have hm : (Generated.hostChunk007[0]).mask = 2380 := by decide +kernel
  have hv : ((Generated.hostChunk007[0]).induced.toList, (Generated.hostChunk007[0]).complement.toList) =
      ([0, 5, 5, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0084]

theorem fixed_values_0085 :
    (fixedDensityCounts (maskGraph 7 2381), fixedComplementCounts (maskGraph 7 2381)) =
      ([0, 3, 6, 0, 0, 1, 0, 4, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0085_semantics :
    ((Generated.hostChunk007[1]).induced.toList, (Generated.hostChunk007[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[1]).mask)) := by
  have hm : (Generated.hostChunk007[1]).mask = 2381 := by decide +kernel
  have hv : ((Generated.hostChunk007[1]).induced.toList, (Generated.hostChunk007[1]).complement.toList) =
      ([0, 3, 6, 0, 0, 1, 0, 4, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0085]

theorem fixed_values_0086 :
    (fixedDensityCounts (maskGraph 7 2383), fixedComplementCounts (maskGraph 7 2383)) =
      ([0, 2, 5, 0, 0, 3, 0, 2, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0086_semantics :
    ((Generated.hostChunk007[2]).induced.toList, (Generated.hostChunk007[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[2]).mask)) := by
  have hm : (Generated.hostChunk007[2]).mask = 2383 := by decide +kernel
  have hv : ((Generated.hostChunk007[2]).induced.toList, (Generated.hostChunk007[2]).complement.toList) =
      ([0, 2, 5, 0, 0, 3, 0, 2, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0086]

theorem fixed_values_0087 :
    (fixedDensityCounts (maskGraph 7 2387), fixedComplementCounts (maskGraph 7 2387)) =
      ([0, 3, 6, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0087_semantics :
    ((Generated.hostChunk007[3]).induced.toList, (Generated.hostChunk007[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[3]).mask)) := by
  have hm : (Generated.hostChunk007[3]).mask = 2387 := by decide +kernel
  have hv : ((Generated.hostChunk007[3]).induced.toList, (Generated.hostChunk007[3]).complement.toList) =
      ([0, 3, 6, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0087]

theorem fixed_values_0088 :
    (fixedDensityCounts (maskGraph 7 2388), fixedComplementCounts (maskGraph 7 2388)) =
      ([0, 3, 6, 0, 0, 0, 3, 5, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0088_semantics :
    ((Generated.hostChunk007[4]).induced.toList, (Generated.hostChunk007[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[4]).mask)) := by
  have hm : (Generated.hostChunk007[4]).mask = 2388 := by decide +kernel
  have hv : ((Generated.hostChunk007[4]).induced.toList, (Generated.hostChunk007[4]).complement.toList) =
      ([0, 3, 6, 0, 0, 0, 3, 5, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0088]

theorem fixed_values_0089 :
    (fixedDensityCounts (maskGraph 7 2389), fixedComplementCounts (maskGraph 7 2389)) =
      ([0, 3, 4, 2, 0, 0, 0, 7, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0089_semantics :
    ((Generated.hostChunk007[5]).induced.toList, (Generated.hostChunk007[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[5]).mask)) := by
  have hm : (Generated.hostChunk007[5]).mask = 2389 := by decide +kernel
  have hv : ((Generated.hostChunk007[5]).induced.toList, (Generated.hostChunk007[5]).complement.toList) =
      ([0, 3, 4, 2, 0, 0, 0, 7, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0089]

theorem fixed_values_0090 :
    (fixedDensityCounts (maskGraph 7 2390), fixedComplementCounts (maskGraph 7 2390)) =
      ([0, 2, 5, 0, 0, 1, 2, 4, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0090_semantics :
    ((Generated.hostChunk007[6]).induced.toList, (Generated.hostChunk007[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[6]).mask)) := by
  have hm : (Generated.hostChunk007[6]).mask = 2390 := by decide +kernel
  have hv : ((Generated.hostChunk007[6]).induced.toList, (Generated.hostChunk007[6]).complement.toList) =
      ([0, 2, 5, 0, 0, 1, 2, 4, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0090]

theorem fixed_values_0091 :
    (fixedDensityCounts (maskGraph 7 2391), fixedComplementCounts (maskGraph 7 2391)) =
      ([0, 2, 4, 1, 0, 1, 0, 4, 4, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0091_semantics :
    ((Generated.hostChunk007[7]).induced.toList, (Generated.hostChunk007[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[7]).mask)) := by
  have hm : (Generated.hostChunk007[7]).mask = 2391 := by decide +kernel
  have hv : ((Generated.hostChunk007[7]).induced.toList, (Generated.hostChunk007[7]).complement.toList) =
      ([0, 2, 4, 1, 0, 1, 0, 4, 4, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0091]

theorem fixed_values_0092 :
    (fixedDensityCounts (maskGraph 7 2396), fixedComplementCounts (maskGraph 7 2396)) =
      ([0, 2, 4, 1, 0, 0, 1, 8, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0092_semantics :
    ((Generated.hostChunk007[8]).induced.toList, (Generated.hostChunk007[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[8]).mask)) := by
  have hm : (Generated.hostChunk007[8]).mask = 2396 := by decide +kernel
  have hv : ((Generated.hostChunk007[8]).induced.toList, (Generated.hostChunk007[8]).complement.toList) =
      ([0, 2, 4, 1, 0, 0, 1, 8, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0092]

theorem fixed_values_0093 :
    (fixedDensityCounts (maskGraph 7 2397), fixedComplementCounts (maskGraph 7 2397)) =
      ([0, 2, 3, 2, 0, 0, 0, 5, 3, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0093_semantics :
    ((Generated.hostChunk007[9]).induced.toList, (Generated.hostChunk007[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[9]).mask)) := by
  have hm : (Generated.hostChunk007[9]).mask = 2397 := by decide +kernel
  have hv : ((Generated.hostChunk007[9]).induced.toList, (Generated.hostChunk007[9]).complement.toList) =
      ([0, 2, 3, 2, 0, 0, 0, 5, 3, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0093]

theorem fixed_values_0094 :
    (fixedDensityCounts (maskGraph 7 2399), fixedComplementCounts (maskGraph 7 2399)) =
      ([0, 2, 2, 3, 0, 0, 0, 2, 5, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0094_semantics :
    ((Generated.hostChunk007[10]).induced.toList, (Generated.hostChunk007[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[10]).mask)) := by
  have hm : (Generated.hostChunk007[10]).mask = 2399 := by decide +kernel
  have hv : ((Generated.hostChunk007[10]).induced.toList, (Generated.hostChunk007[10]).complement.toList) =
      ([0, 2, 2, 3, 0, 0, 0, 2, 5, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0094]

theorem fixed_values_0095 :
    (fixedDensityCounts (maskGraph 7 2416), fixedComplementCounts (maskGraph 7 2416)) =
      ([0, 2, 5, 0, 0, 0, 4, 3, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0095_semantics :
    ((Generated.hostChunk007[11]).induced.toList, (Generated.hostChunk007[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk007[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk007[11]).mask)) := by
  have hm : (Generated.hostChunk007[11]).mask = 2416 := by decide +kernel
  have hv : ((Generated.hostChunk007[11]).induced.toList, (Generated.hostChunk007[11]).complement.toList) =
      ([0, 2, 5, 0, 0, 0, 4, 3, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0095]

theorem fixed_chunk_007_semantics :
    ∀ h ∈ Generated.hostChunk007.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk007.toList = [Generated.hostChunk007[0], Generated.hostChunk007[1], Generated.hostChunk007[2], Generated.hostChunk007[3], Generated.hostChunk007[4], Generated.hostChunk007[5], Generated.hostChunk007[6], Generated.hostChunk007[7], Generated.hostChunk007[8], Generated.hostChunk007[9], Generated.hostChunk007[10], Generated.hostChunk007[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0084_semantics
  · exact fixed_host_0085_semantics
  · exact fixed_host_0086_semantics
  · exact fixed_host_0087_semantics
  · exact fixed_host_0088_semantics
  · exact fixed_host_0089_semantics
  · exact fixed_host_0090_semantics
  · exact fixed_host_0091_semantics
  · exact fixed_host_0092_semantics
  · exact fixed_host_0093_semantics
  · exact fixed_host_0094_semantics
  · exact fixed_host_0095_semantics

end InducedPentagons.Paper

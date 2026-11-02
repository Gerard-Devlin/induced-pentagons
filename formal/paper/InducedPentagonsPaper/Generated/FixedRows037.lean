import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData037
import InducedPentagonsPaper.Generated.FixedRows029

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0444 :
    (fixedDensityCounts (maskGraph 7 39923), fixedComplementCounts (maskGraph 7 39923)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 3, 2, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0444_semantics :
    ((Generated.hostChunk037[0]).induced.toList, (Generated.hostChunk037[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[0]).mask)) := by
  have hm : (Generated.hostChunk037[0]).mask = 39923 := by decide +kernel
  have hv : ((Generated.hostChunk037[0]).induced.toList, (Generated.hostChunk037[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 3, 2, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0444]

theorem fixed_values_0445 :
    (fixedDensityCounts (maskGraph 7 39926), fixedComplementCounts (maskGraph 7 39926)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 2, 3, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0445_semantics :
    ((Generated.hostChunk037[1]).induced.toList, (Generated.hostChunk037[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[1]).mask)) := by
  have hm : (Generated.hostChunk037[1]).mask = 39926 := by decide +kernel
  have hv : ((Generated.hostChunk037[1]).induced.toList, (Generated.hostChunk037[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 2, 3, 1, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0445]

theorem fixed_values_0446 :
    (fixedDensityCounts (maskGraph 7 39927), fixedComplementCounts (maskGraph 7 39927)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 4, 2, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0446_semantics :
    ((Generated.hostChunk037[2]).induced.toList, (Generated.hostChunk037[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[2]).mask)) := by
  have hm : (Generated.hostChunk037[2]).mask = 39927 := by decide +kernel
  have hv : ((Generated.hostChunk037[2]).induced.toList, (Generated.hostChunk037[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 4, 2, 0, 0, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0446]

theorem fixed_values_0447 :
    (fixedDensityCounts (maskGraph 7 39934), fixedComplementCounts (maskGraph 7 39934)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0447_semantics :
    ((Generated.hostChunk037[3]).induced.toList, (Generated.hostChunk037[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[3]).mask)) := by
  have hm : (Generated.hostChunk037[3]).mask = 39934 := by decide +kernel
  have hv : ((Generated.hostChunk037[3]).induced.toList, (Generated.hostChunk037[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0447]

theorem fixed_values_0448 :
    (fixedDensityCounts (maskGraph 7 39935), fixedComplementCounts (maskGraph 7 39935)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0448_semantics :
    ((Generated.hostChunk037[4]).induced.toList, (Generated.hostChunk037[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[4]).mask)) := by
  have hm : (Generated.hostChunk037[4]).mask = 39935 := by decide +kernel
  have hv : ((Generated.hostChunk037[4]).induced.toList, (Generated.hostChunk037[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0448]

theorem fixed_values_0449 :
    (fixedDensityCounts (maskGraph 7 40496), fixedComplementCounts (maskGraph 7 40496)) =
      ([0, 0, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0449_semantics :
    ((Generated.hostChunk037[5]).induced.toList, (Generated.hostChunk037[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[5]).mask)) := by
  have hm : (Generated.hostChunk037[5]).mask = 40496 := by decide +kernel
  have hv : ((Generated.hostChunk037[5]).induced.toList, (Generated.hostChunk037[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0449]

theorem fixed_values_0450 :
    (fixedDensityCounts (maskGraph 7 40497), fixedComplementCounts (maskGraph 7 40497)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0450_semantics :
    ((Generated.hostChunk037[6]).induced.toList, (Generated.hostChunk037[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[6]).mask)) := by
  have hm : (Generated.hostChunk037[6]).mask = 40497 := by decide +kernel
  have hv : ((Generated.hostChunk037[6]).induced.toList, (Generated.hostChunk037[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0450]

theorem fixed_values_0451 :
    (fixedDensityCounts (maskGraph 7 40498), fixedComplementCounts (maskGraph 7 40498)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 1, 6, 2, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0451_semantics :
    ((Generated.hostChunk037[7]).induced.toList, (Generated.hostChunk037[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[7]).mask)) := by
  have hm : (Generated.hostChunk037[7]).mask = 40498 := by decide +kernel
  have hv : ((Generated.hostChunk037[7]).induced.toList, (Generated.hostChunk037[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 1, 6, 2, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0451]

theorem fixed_values_0452 :
    (fixedDensityCounts (maskGraph 7 40499), fixedComplementCounts (maskGraph 7 40499)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0452_semantics :
    ((Generated.hostChunk037[8]).induced.toList, (Generated.hostChunk037[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[8]).mask)) := by
  have hm : (Generated.hostChunk037[8]).mask = 40499 := by decide +kernel
  have hv : ((Generated.hostChunk037[8]).induced.toList, (Generated.hostChunk037[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0452]

theorem fixed_values_0453 :
    (fixedDensityCounts (maskGraph 7 40502), fixedComplementCounts (maskGraph 7 40502)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 2, 1, 1, 1, 4, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0453_semantics :
    ((Generated.hostChunk037[9]).induced.toList, (Generated.hostChunk037[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[9]).mask)) := by
  have hm : (Generated.hostChunk037[9]).mask = 40502 := by decide +kernel
  have hv : ((Generated.hostChunk037[9]).induced.toList, (Generated.hostChunk037[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 2, 1, 1, 1, 4, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0453]

theorem fixed_values_0454 :
    (fixedDensityCounts (maskGraph 7 40503), fixedComplementCounts (maskGraph 7 40503)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 2, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 4, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0454_semantics :
    ((Generated.hostChunk037[10]).induced.toList, (Generated.hostChunk037[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[10]).mask)) := by
  have hm : (Generated.hostChunk037[10]).mask = 40503 := by decide +kernel
  have hv : ((Generated.hostChunk037[10]).induced.toList, (Generated.hostChunk037[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 2, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 4, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0454]

theorem fixed_values_0455 :
    (fixedDensityCounts (maskGraph 7 40510), fixedComplementCounts (maskGraph 7 40510)) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 2, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0455_semantics :
    ((Generated.hostChunk037[11]).induced.toList, (Generated.hostChunk037[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk037[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk037[11]).mask)) := by
  have hm : (Generated.hostChunk037[11]).mask = 40510 := by decide +kernel
  have hv : ((Generated.hostChunk037[11]).induced.toList, (Generated.hostChunk037[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 2, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0455]

theorem fixed_chunk_037_semantics :
    ∀ h ∈ Generated.hostChunk037.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk037.toList = [Generated.hostChunk037[0], Generated.hostChunk037[1], Generated.hostChunk037[2], Generated.hostChunk037[3], Generated.hostChunk037[4], Generated.hostChunk037[5], Generated.hostChunk037[6], Generated.hostChunk037[7], Generated.hostChunk037[8], Generated.hostChunk037[9], Generated.hostChunk037[10], Generated.hostChunk037[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0444_semantics
  · exact fixed_host_0445_semantics
  · exact fixed_host_0446_semantics
  · exact fixed_host_0447_semantics
  · exact fixed_host_0448_semantics
  · exact fixed_host_0449_semantics
  · exact fixed_host_0450_semantics
  · exact fixed_host_0451_semantics
  · exact fixed_host_0452_semantics
  · exact fixed_host_0453_semantics
  · exact fixed_host_0454_semantics
  · exact fixed_host_0455_semantics

end InducedPentagons.Paper

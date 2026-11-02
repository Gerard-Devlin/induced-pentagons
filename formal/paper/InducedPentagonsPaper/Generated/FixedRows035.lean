import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData035
import InducedPentagonsPaper.Generated.FixedRows027

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0420 :
    (fixedDensityCounts (maskGraph 7 39655), fixedComplementCounts (maskGraph 7 39655)) =
      ([0, 0, 0, 0, 0, 1, 0, 5, 2, 0, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0420_semantics :
    ((Generated.hostChunk035[0]).induced.toList, (Generated.hostChunk035[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[0]).mask)) := by
  have hm : (Generated.hostChunk035[0]).mask = 39655 := by decide +kernel
  have hv : ((Generated.hostChunk035[0]).induced.toList, (Generated.hostChunk035[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 5, 2, 0, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0420]

theorem fixed_values_0421 :
    (fixedDensityCounts (maskGraph 7 39658), fixedComplementCounts (maskGraph 7 39658)) =
      ([0, 0, 0, 0, 0, 1, 0, 4, 2, 2, 0, 0, 0, 2, 3, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0421_semantics :
    ((Generated.hostChunk035[1]).induced.toList, (Generated.hostChunk035[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[1]).mask)) := by
  have hm : (Generated.hostChunk035[1]).mask = 39658 := by decide +kernel
  have hv : ((Generated.hostChunk035[1]).induced.toList, (Generated.hostChunk035[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 4, 2, 2, 0, 0, 0, 2, 3, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0421]

theorem fixed_values_0422 :
    (fixedDensityCounts (maskGraph 7 39659), fixedComplementCounts (maskGraph 7 39659)) =
      ([0, 0, 0, 0, 0, 1, 0, 4, 2, 0, 2, 0, 0, 2, 0, 1, 2, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0422_semantics :
    ((Generated.hostChunk035[2]).induced.toList, (Generated.hostChunk035[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[2]).mask)) := by
  have hm : (Generated.hostChunk035[2]).mask = 39659 := by decide +kernel
  have hv : ((Generated.hostChunk035[2]).induced.toList, (Generated.hostChunk035[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 4, 2, 0, 2, 0, 0, 2, 0, 1, 2, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0422]

theorem fixed_values_0423 :
    (fixedDensityCounts (maskGraph 7 39662), fixedComplementCounts (maskGraph 7 39662)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 4, 1, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 2, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0423_semantics :
    ((Generated.hostChunk035[3]).induced.toList, (Generated.hostChunk035[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[3]).mask)) := by
  have hm : (Generated.hostChunk035[3]).mask = 39662 := by decide +kernel
  have hv : ((Generated.hostChunk035[3]).induced.toList, (Generated.hostChunk035[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 4, 1, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 2, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0423]

theorem fixed_values_0424 :
    (fixedDensityCounts (maskGraph 7 39663), fixedComplementCounts (maskGraph 7 39663)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0424_semantics :
    ((Generated.hostChunk035[4]).induced.toList, (Generated.hostChunk035[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[4]).mask)) := by
  have hm : (Generated.hostChunk035[4]).mask = 39663 := by decide +kernel
  have hv : ((Generated.hostChunk035[4]).induced.toList, (Generated.hostChunk035[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0424]

theorem fixed_values_0425 :
    (fixedDensityCounts (maskGraph 7 39664), fixedComplementCounts (maskGraph 7 39664)) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 1, 5, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0425_semantics :
    ((Generated.hostChunk035[5]).induced.toList, (Generated.hostChunk035[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[5]).mask)) := by
  have hm : (Generated.hostChunk035[5]).mask = 39664 := by decide +kernel
  have hv : ((Generated.hostChunk035[5]).induced.toList, (Generated.hostChunk035[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 1, 5, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0425]

theorem fixed_values_0426 :
    (fixedDensityCounts (maskGraph 7 39665), fixedComplementCounts (maskGraph 7 39665)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 2, 3, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 2, 3, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0426_semantics :
    ((Generated.hostChunk035[6]).induced.toList, (Generated.hostChunk035[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[6]).mask)) := by
  have hm : (Generated.hostChunk035[6]).mask = 39665 := by decide +kernel
  have hv : ((Generated.hostChunk035[6]).induced.toList, (Generated.hostChunk035[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 2, 3, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 2, 3, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0426]

theorem fixed_values_0427 :
    (fixedDensityCounts (maskGraph 7 39666), fixedComplementCounts (maskGraph 7 39666)) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 1, 2, 3, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 0, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0427_semantics :
    ((Generated.hostChunk035[7]).induced.toList, (Generated.hostChunk035[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[7]).mask)) := by
  have hm : (Generated.hostChunk035[7]).mask = 39666 := by decide +kernel
  have hv : ((Generated.hostChunk035[7]).induced.toList, (Generated.hostChunk035[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 1, 2, 3, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 0, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0427]

theorem fixed_values_0428 :
    (fixedDensityCounts (maskGraph 7 39667), fixedComplementCounts (maskGraph 7 39667)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0428_semantics :
    ((Generated.hostChunk035[8]).induced.toList, (Generated.hostChunk035[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[8]).mask)) := by
  have hm : (Generated.hostChunk035[8]).mask = 39667 := by decide +kernel
  have hv : ((Generated.hostChunk035[8]).induced.toList, (Generated.hostChunk035[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0428]

theorem fixed_values_0429 :
    (fixedDensityCounts (maskGraph 7 39670), fixedComplementCounts (maskGraph 7 39670)) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 4, 1, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0429_semantics :
    ((Generated.hostChunk035[9]).induced.toList, (Generated.hostChunk035[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[9]).mask)) := by
  have hm : (Generated.hostChunk035[9]).mask = 39670 := by decide +kernel
  have hv : ((Generated.hostChunk035[9]).induced.toList, (Generated.hostChunk035[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 4, 1, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0429]

theorem fixed_values_0430 :
    (fixedDensityCounts (maskGraph 7 39671), fixedComplementCounts (maskGraph 7 39671)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 5, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0430_semantics :
    ((Generated.hostChunk035[10]).induced.toList, (Generated.hostChunk035[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[10]).mask)) := by
  have hm : (Generated.hostChunk035[10]).mask = 39671 := by decide +kernel
  have hv : ((Generated.hostChunk035[10]).induced.toList, (Generated.hostChunk035[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 5, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0430]

theorem fixed_values_0431 :
    (fixedDensityCounts (maskGraph 7 39672), fixedComplementCounts (maskGraph 7 39672)) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 3, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0431_semantics :
    ((Generated.hostChunk035[11]).induced.toList, (Generated.hostChunk035[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk035[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk035[11]).mask)) := by
  have hm : (Generated.hostChunk035[11]).mask = 39672 := by decide +kernel
  have hv : ((Generated.hostChunk035[11]).induced.toList, (Generated.hostChunk035[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 3, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0431]

theorem fixed_chunk_035_semantics :
    ∀ h ∈ Generated.hostChunk035.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk035.toList = [Generated.hostChunk035[0], Generated.hostChunk035[1], Generated.hostChunk035[2], Generated.hostChunk035[3], Generated.hostChunk035[4], Generated.hostChunk035[5], Generated.hostChunk035[6], Generated.hostChunk035[7], Generated.hostChunk035[8], Generated.hostChunk035[9], Generated.hostChunk035[10], Generated.hostChunk035[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0420_semantics
  · exact fixed_host_0421_semantics
  · exact fixed_host_0422_semantics
  · exact fixed_host_0423_semantics
  · exact fixed_host_0424_semantics
  · exact fixed_host_0425_semantics
  · exact fixed_host_0426_semantics
  · exact fixed_host_0427_semantics
  · exact fixed_host_0428_semantics
  · exact fixed_host_0429_semantics
  · exact fixed_host_0430_semantics
  · exact fixed_host_0431_semantics

end InducedPentagons.Paper

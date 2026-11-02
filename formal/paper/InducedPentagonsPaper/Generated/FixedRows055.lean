import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData055
import InducedPentagonsPaper.Generated.FixedRows047

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0660 :
    (fixedDensityCounts (maskGraph 7 48119), fixedComplementCounts (maskGraph 7 48119)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 2, 0, 2, 0, 0, 1, 0, 0, 3, 2, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0660_semantics :
    ((Generated.hostChunk055[0]).induced.toList, (Generated.hostChunk055[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[0]).mask)) := by
  have hm : (Generated.hostChunk055[0]).mask = 48119 := by decide +kernel
  have hv : ((Generated.hostChunk055[0]).induced.toList, (Generated.hostChunk055[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 2, 0, 2, 0, 0, 1, 0, 0, 3, 2, 0, 0, 0, 2, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0660]

theorem fixed_values_0661 :
    (fixedDensityCounts (maskGraph 7 48124), fixedComplementCounts (maskGraph 7 48124)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 4, 0, 0, 0, 1, 0, 3, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 4, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0661_semantics :
    ((Generated.hostChunk055[1]).induced.toList, (Generated.hostChunk055[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[1]).mask)) := by
  have hm : (Generated.hostChunk055[1]).mask = 48124 := by decide +kernel
  have hv : ((Generated.hostChunk055[1]).induced.toList, (Generated.hostChunk055[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 4, 0, 0, 0, 1, 0, 3, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 4, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0661]

theorem fixed_values_0662 :
    (fixedDensityCounts (maskGraph 7 48125), fixedComplementCounts (maskGraph 7 48125)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0662_semantics :
    ((Generated.hostChunk055[2]).induced.toList, (Generated.hostChunk055[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[2]).mask)) := by
  have hm : (Generated.hostChunk055[2]).mask = 48125 := by decide +kernel
  have hv : ((Generated.hostChunk055[2]).induced.toList, (Generated.hostChunk055[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 2, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0662]

theorem fixed_values_0663 :
    (fixedDensityCounts (maskGraph 7 48127), fixedComplementCounts (maskGraph 7 48127)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0663_semantics :
    ((Generated.hostChunk055[3]).induced.toList, (Generated.hostChunk055[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[3]).mask)) := by
  have hm : (Generated.hostChunk055[3]).mask = 48127 := by decide +kernel
  have hv : ((Generated.hostChunk055[3]).induced.toList, (Generated.hostChunk055[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0663]

theorem fixed_values_0664 :
    (fixedDensityCounts (maskGraph 7 48560), fixedComplementCounts (maskGraph 7 48560)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 11, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0664_semantics :
    ((Generated.hostChunk055[4]).induced.toList, (Generated.hostChunk055[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[4]).mask)) := by
  have hm : (Generated.hostChunk055[4]).mask = 48560 := by decide +kernel
  have hv : ((Generated.hostChunk055[4]).induced.toList, (Generated.hostChunk055[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 11, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0664]

theorem fixed_values_0665 :
    (fixedDensityCounts (maskGraph 7 48561), fixedComplementCounts (maskGraph 7 48561)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 1, 5, 3, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0665_semantics :
    ((Generated.hostChunk055[5]).induced.toList, (Generated.hostChunk055[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[5]).mask)) := by
  have hm : (Generated.hostChunk055[5]).mask = 48561 := by decide +kernel
  have hv : ((Generated.hostChunk055[5]).induced.toList, (Generated.hostChunk055[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 1, 5, 3, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0665]

theorem fixed_values_0666 :
    (fixedDensityCounts (maskGraph 7 48563), fixedComplementCounts (maskGraph 7 48563)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 3, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0666_semantics :
    ((Generated.hostChunk055[6]).induced.toList, (Generated.hostChunk055[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[6]).mask)) := by
  have hm : (Generated.hostChunk055[6]).mask = 48563 := by decide +kernel
  have hv : ((Generated.hostChunk055[6]).induced.toList, (Generated.hostChunk055[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 3, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0666]

theorem fixed_values_0667 :
    (fixedDensityCounts (maskGraph 7 48564), fixedComplementCounts (maskGraph 7 48564)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 7, 0, 4, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0667_semantics :
    ((Generated.hostChunk055[7]).induced.toList, (Generated.hostChunk055[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[7]).mask)) := by
  have hm : (Generated.hostChunk055[7]).mask = 48564 := by decide +kernel
  have hv : ((Generated.hostChunk055[7]).induced.toList, (Generated.hostChunk055[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 7, 0, 4, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0667]

theorem fixed_values_0668 :
    (fixedDensityCounts (maskGraph 7 48565), fixedComplementCounts (maskGraph 7 48565)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 1, 1, 1, 0, 0, 0, 0, 3, 4, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0668_semantics :
    ((Generated.hostChunk055[8]).induced.toList, (Generated.hostChunk055[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[8]).mask)) := by
  have hm : (Generated.hostChunk055[8]).mask = 48565 := by decide +kernel
  have hv : ((Generated.hostChunk055[8]).induced.toList, (Generated.hostChunk055[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 1, 1, 1, 0, 0, 0, 0, 3, 4, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0668]

theorem fixed_values_0669 :
    (fixedDensityCounts (maskGraph 7 48567), fixedComplementCounts (maskGraph 7 48567)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 2, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0669_semantics :
    ((Generated.hostChunk055[9]).induced.toList, (Generated.hostChunk055[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[9]).mask)) := by
  have hm : (Generated.hostChunk055[9]).mask = 48567 := by decide +kernel
  have hv : ((Generated.hostChunk055[9]).induced.toList, (Generated.hostChunk055[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 2, 4, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0669]

theorem fixed_values_0670 :
    (fixedDensityCounts (maskGraph 7 48572), fixedComplementCounts (maskGraph 7 48572)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 8, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0670_semantics :
    ((Generated.hostChunk055[10]).induced.toList, (Generated.hostChunk055[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[10]).mask)) := by
  have hm : (Generated.hostChunk055[10]).mask = 48572 := by decide +kernel
  have hv : ((Generated.hostChunk055[10]).induced.toList, (Generated.hostChunk055[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 8, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0670]

theorem fixed_values_0671 :
    (fixedDensityCounts (maskGraph 7 48573), fixedComplementCounts (maskGraph 7 48573)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 1, 5, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0671_semantics :
    ((Generated.hostChunk055[11]).induced.toList, (Generated.hostChunk055[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk055[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk055[11]).mask)) := by
  have hm : (Generated.hostChunk055[11]).mask = 48573 := by decide +kernel
  have hv : ((Generated.hostChunk055[11]).induced.toList, (Generated.hostChunk055[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 1, 5, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0671]

theorem fixed_chunk_055_semantics :
    ∀ h ∈ Generated.hostChunk055.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk055.toList = [Generated.hostChunk055[0], Generated.hostChunk055[1], Generated.hostChunk055[2], Generated.hostChunk055[3], Generated.hostChunk055[4], Generated.hostChunk055[5], Generated.hostChunk055[6], Generated.hostChunk055[7], Generated.hostChunk055[8], Generated.hostChunk055[9], Generated.hostChunk055[10], Generated.hostChunk055[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0660_semantics
  · exact fixed_host_0661_semantics
  · exact fixed_host_0662_semantics
  · exact fixed_host_0663_semantics
  · exact fixed_host_0664_semantics
  · exact fixed_host_0665_semantics
  · exact fixed_host_0666_semantics
  · exact fixed_host_0667_semantics
  · exact fixed_host_0668_semantics
  · exact fixed_host_0669_semantics
  · exact fixed_host_0670_semantics
  · exact fixed_host_0671_semantics

end InducedPentagons.Paper

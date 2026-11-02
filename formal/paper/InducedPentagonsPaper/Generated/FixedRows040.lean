import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData040
import InducedPentagonsPaper.Generated.FixedRows032

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0480 :
    (fixedDensityCounts (maskGraph 7 41955), fixedComplementCounts (maskGraph 7 41955)) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 4, 2, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0480_semantics :
    ((Generated.hostChunk040[0]).induced.toList, (Generated.hostChunk040[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[0]).mask)) := by
  have hm : (Generated.hostChunk040[0]).mask = 41955 := by decide +kernel
  have hv : ((Generated.hostChunk040[0]).induced.toList, (Generated.hostChunk040[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 2, 2, 4, 2, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0480]

theorem fixed_values_0481 :
    (fixedDensityCounts (maskGraph 7 41958), fixedComplementCounts (maskGraph 7 41958)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 4, 1, 2, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0481_semantics :
    ((Generated.hostChunk040[1]).induced.toList, (Generated.hostChunk040[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[1]).mask)) := by
  have hm : (Generated.hostChunk040[1]).mask = 41958 := by decide +kernel
  have hv : ((Generated.hostChunk040[1]).induced.toList, (Generated.hostChunk040[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 4, 1, 2, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0481]

theorem fixed_values_0482 :
    (fixedDensityCounts (maskGraph 7 41959), fixedComplementCounts (maskGraph 7 41959)) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 3, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0482_semantics :
    ((Generated.hostChunk040[2]).induced.toList, (Generated.hostChunk040[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[2]).mask)) := by
  have hm : (Generated.hostChunk040[2]).mask = 41959 := by decide +kernel
  have hv : ((Generated.hostChunk040[2]).induced.toList, (Generated.hostChunk040[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 3, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0482]

theorem fixed_values_0483 :
    (fixedDensityCounts (maskGraph 7 41964), fixedComplementCounts (maskGraph 7 41964)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 6, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0483_semantics :
    ((Generated.hostChunk040[3]).induced.toList, (Generated.hostChunk040[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[3]).mask)) := by
  have hm : (Generated.hostChunk040[3]).mask = 41964 := by decide +kernel
  have hv : ((Generated.hostChunk040[3]).induced.toList, (Generated.hostChunk040[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 6, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0483]

theorem fixed_values_0484 :
    (fixedDensityCounts (maskGraph 7 41965), fixedComplementCounts (maskGraph 7 41965)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 6, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0484_semantics :
    ((Generated.hostChunk040[4]).induced.toList, (Generated.hostChunk040[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[4]).mask)) := by
  have hm : (Generated.hostChunk040[4]).mask = 41965 := by decide +kernel
  have hv : ((Generated.hostChunk040[4]).induced.toList, (Generated.hostChunk040[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 6, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0484]

theorem fixed_values_0485 :
    (fixedDensityCounts (maskGraph 7 41966), fixedComplementCounts (maskGraph 7 41966)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 2, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0485_semantics :
    ((Generated.hostChunk040[5]).induced.toList, (Generated.hostChunk040[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[5]).mask)) := by
  have hm : (Generated.hostChunk040[5]).mask = 41966 := by decide +kernel
  have hv : ((Generated.hostChunk040[5]).induced.toList, (Generated.hostChunk040[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 2, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0485]

theorem fixed_values_0486 :
    (fixedDensityCounts (maskGraph 7 41967), fixedComplementCounts (maskGraph 7 41967)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0486_semantics :
    ((Generated.hostChunk040[6]).induced.toList, (Generated.hostChunk040[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[6]).mask)) := by
  have hm : (Generated.hostChunk040[6]).mask = 41967 := by decide +kernel
  have hv : ((Generated.hostChunk040[6]).induced.toList, (Generated.hostChunk040[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0486]

theorem fixed_values_0487 :
    (fixedDensityCounts (maskGraph 7 41982), fixedComplementCounts (maskGraph 7 41982)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0487_semantics :
    ((Generated.hostChunk040[7]).induced.toList, (Generated.hostChunk040[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[7]).mask)) := by
  have hm : (Generated.hostChunk040[7]).mask = 41982 := by decide +kernel
  have hv : ((Generated.hostChunk040[7]).induced.toList, (Generated.hostChunk040[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0487]

theorem fixed_values_0488 :
    (fixedDensityCounts (maskGraph 7 41983), fixedComplementCounts (maskGraph 7 41983)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0488_semantics :
    ((Generated.hostChunk040[8]).induced.toList, (Generated.hostChunk040[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[8]).mask)) := by
  have hm : (Generated.hostChunk040[8]).mask = 41983 := by decide +kernel
  have hv : ((Generated.hostChunk040[8]).induced.toList, (Generated.hostChunk040[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 4, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0488]

theorem fixed_values_0489 :
    (fixedDensityCounts (maskGraph 7 42047), fixedComplementCounts (maskGraph 7 42047)) =
      ([0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0489_semantics :
    ((Generated.hostChunk040[9]).induced.toList, (Generated.hostChunk040[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[9]).mask)) := by
  have hm : (Generated.hostChunk040[9]).mask = 42047 := by decide +kernel
  have hv : ((Generated.hostChunk040[9]).induced.toList, (Generated.hostChunk040[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0489]

theorem fixed_values_0490 :
    (fixedDensityCounts (maskGraph 7 42096), fixedComplementCounts (maskGraph 7 42096)) =
      ([0, 0, 0, 0, 0, 0, 5, 10, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0490_semantics :
    ((Generated.hostChunk040[10]).induced.toList, (Generated.hostChunk040[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[10]).mask)) := by
  have hm : (Generated.hostChunk040[10]).mask = 42096 := by decide +kernel
  have hv : ((Generated.hostChunk040[10]).induced.toList, (Generated.hostChunk040[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 5, 10, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0490]

theorem fixed_values_0491 :
    (fixedDensityCounts (maskGraph 7 42097), fixedComplementCounts (maskGraph 7 42097)) =
      ([0, 0, 0, 0, 0, 0, 3, 4, 4, 6, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0491_semantics :
    ((Generated.hostChunk040[11]).induced.toList, (Generated.hostChunk040[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk040[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk040[11]).mask)) := by
  have hm : (Generated.hostChunk040[11]).mask = 42097 := by decide +kernel
  have hv : ((Generated.hostChunk040[11]).induced.toList, (Generated.hostChunk040[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 3, 4, 4, 6, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0491]

theorem fixed_chunk_040_semantics :
    ∀ h ∈ Generated.hostChunk040.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk040.toList = [Generated.hostChunk040[0], Generated.hostChunk040[1], Generated.hostChunk040[2], Generated.hostChunk040[3], Generated.hostChunk040[4], Generated.hostChunk040[5], Generated.hostChunk040[6], Generated.hostChunk040[7], Generated.hostChunk040[8], Generated.hostChunk040[9], Generated.hostChunk040[10], Generated.hostChunk040[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0480_semantics
  · exact fixed_host_0481_semantics
  · exact fixed_host_0482_semantics
  · exact fixed_host_0483_semantics
  · exact fixed_host_0484_semantics
  · exact fixed_host_0485_semantics
  · exact fixed_host_0486_semantics
  · exact fixed_host_0487_semantics
  · exact fixed_host_0488_semantics
  · exact fixed_host_0489_semantics
  · exact fixed_host_0490_semantics
  · exact fixed_host_0491_semantics

end InducedPentagons.Paper

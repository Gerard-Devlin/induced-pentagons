import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData057
import InducedPentagonsPaper.Generated.FixedRows049

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0684 :
    (fixedDensityCounts (maskGraph 7 48691), fixedComplementCounts (maskGraph 7 48691)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 3, 5, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0684_semantics :
    ((Generated.hostChunk057[0]).induced.toList, (Generated.hostChunk057[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[0]).mask)) := by
  have hm : (Generated.hostChunk057[0]).mask = 48691 := by decide +kernel
  have hv : ((Generated.hostChunk057[0]).induced.toList, (Generated.hostChunk057[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 3, 5, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0684]

theorem fixed_values_0685 :
    (fixedDensityCounts (maskGraph 7 48692), fixedComplementCounts (maskGraph 7 48692)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 1, 0, 6, 0, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0685_semantics :
    ((Generated.hostChunk057[1]).induced.toList, (Generated.hostChunk057[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[1]).mask)) := by
  have hm : (Generated.hostChunk057[1]).mask = 48692 := by decide +kernel
  have hv : ((Generated.hostChunk057[1]).induced.toList, (Generated.hostChunk057[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 1, 0, 6, 0, 4, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0685]

theorem fixed_values_0686 :
    (fixedDensityCounts (maskGraph 7 48693), fixedComplementCounts (maskGraph 7 48693)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 3, 0, 1, 1, 0, 0, 0, 2, 7, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0686_semantics :
    ((Generated.hostChunk057[2]).induced.toList, (Generated.hostChunk057[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[2]).mask)) := by
  have hm : (Generated.hostChunk057[2]).mask = 48693 := by decide +kernel
  have hv : ((Generated.hostChunk057[2]).induced.toList, (Generated.hostChunk057[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 3, 0, 1, 1, 0, 0, 0, 2, 7, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0686]

theorem fixed_values_0687 :
    (fixedDensityCounts (maskGraph 7 48694), fixedComplementCounts (maskGraph 7 48694)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 5, 2, 1, 1, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0687_semantics :
    ((Generated.hostChunk057[3]).induced.toList, (Generated.hostChunk057[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[3]).mask)) := by
  have hm : (Generated.hostChunk057[3]).mask = 48694 := by decide +kernel
  have hv : ((Generated.hostChunk057[3]).induced.toList, (Generated.hostChunk057[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 5, 2, 1, 1, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0687]

theorem fixed_values_0688 :
    (fixedDensityCounts (maskGraph 7 48695), fixedComplementCounts (maskGraph 7 48695)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 1, 4, 3, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0688_semantics :
    ((Generated.hostChunk057[4]).induced.toList, (Generated.hostChunk057[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[4]).mask)) := by
  have hm : (Generated.hostChunk057[4]).mask = 48695 := by decide +kernel
  have hv : ((Generated.hostChunk057[4]).induced.toList, (Generated.hostChunk057[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 1, 4, 3, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0688]

theorem fixed_values_0689 :
    (fixedDensityCounts (maskGraph 7 48700), fixedComplementCounts (maskGraph 7 48700)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 4, 0, 7, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0689_semantics :
    ((Generated.hostChunk057[5]).induced.toList, (Generated.hostChunk057[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[5]).mask)) := by
  have hm : (Generated.hostChunk057[5]).mask = 48700 := by decide +kernel
  have hv : ((Generated.hostChunk057[5]).induced.toList, (Generated.hostChunk057[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 4, 0, 7, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0689]

theorem fixed_values_0690 :
    (fixedDensityCounts (maskGraph 7 48701), fixedComplementCounts (maskGraph 7 48701)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 0, 1, 3, 3, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0690_semantics :
    ((Generated.hostChunk057[6]).induced.toList, (Generated.hostChunk057[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[6]).mask)) := by
  have hm : (Generated.hostChunk057[6]).mask = 48701 := by decide +kernel
  have hv : ((Generated.hostChunk057[6]).induced.toList, (Generated.hostChunk057[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 0, 1, 3, 3, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0690]

theorem fixed_values_0691 :
    (fixedDensityCounts (maskGraph 7 48702), fixedComplementCounts (maskGraph 7 48702)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 1, 1, 5, 2, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0691_semantics :
    ((Generated.hostChunk057[7]).induced.toList, (Generated.hostChunk057[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[7]).mask)) := by
  have hm : (Generated.hostChunk057[7]).mask = 48702 := by decide +kernel
  have hv : ((Generated.hostChunk057[7]).induced.toList, (Generated.hostChunk057[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 2, 2, 0, 0, 1, 1, 5, 2, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0691]

theorem fixed_values_0692 :
    (fixedDensityCounts (maskGraph 7 48703), fixedComplementCounts (maskGraph 7 48703)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 0, 1, 1, 0, 2, 4, 0, 0, 3, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0692_semantics :
    ((Generated.hostChunk057[8]).induced.toList, (Generated.hostChunk057[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[8]).mask)) := by
  have hm : (Generated.hostChunk057[8]).mask = 48703 := by decide +kernel
  have hv : ((Generated.hostChunk057[8]).induced.toList, (Generated.hostChunk057[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 0, 1, 1, 0, 2, 4, 0, 0, 3, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0692]

theorem fixed_values_0693 :
    (fixedDensityCounts (maskGraph 7 48754), fixedComplementCounts (maskGraph 7 48754)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 1, 2, 0, 0, 4, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0693_semantics :
    ((Generated.hostChunk057[9]).induced.toList, (Generated.hostChunk057[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[9]).mask)) := by
  have hm : (Generated.hostChunk057[9]).mask = 48754 := by decide +kernel
  have hv : ((Generated.hostChunk057[9]).induced.toList, (Generated.hostChunk057[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 1, 2, 0, 0, 4, 2, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0693]

theorem fixed_values_0694 :
    (fixedDensityCounts (maskGraph 7 48755), fixedComplementCounts (maskGraph 7 48755)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 2, 2, 2, 2, 3, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0694_semantics :
    ((Generated.hostChunk057[10]).induced.toList, (Generated.hostChunk057[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[10]).mask)) := by
  have hm : (Generated.hostChunk057[10]).mask = 48755 := by decide +kernel
  have hv : ((Generated.hostChunk057[10]).induced.toList, (Generated.hostChunk057[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 2, 2, 2, 2, 3, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0694]

theorem fixed_values_0695 :
    (fixedDensityCounts (maskGraph 7 48756), fixedComplementCounts (maskGraph 7 48756)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 4, 4, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0695_semantics :
    ((Generated.hostChunk057[11]).induced.toList, (Generated.hostChunk057[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk057[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk057[11]).mask)) := by
  have hm : (Generated.hostChunk057[11]).mask = 48756 := by decide +kernel
  have hv : ((Generated.hostChunk057[11]).induced.toList, (Generated.hostChunk057[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 4, 4, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0695]

theorem fixed_chunk_057_semantics :
    ∀ h ∈ Generated.hostChunk057.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk057.toList = [Generated.hostChunk057[0], Generated.hostChunk057[1], Generated.hostChunk057[2], Generated.hostChunk057[3], Generated.hostChunk057[4], Generated.hostChunk057[5], Generated.hostChunk057[6], Generated.hostChunk057[7], Generated.hostChunk057[8], Generated.hostChunk057[9], Generated.hostChunk057[10], Generated.hostChunk057[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0684_semantics
  · exact fixed_host_0685_semantics
  · exact fixed_host_0686_semantics
  · exact fixed_host_0687_semantics
  · exact fixed_host_0688_semantics
  · exact fixed_host_0689_semantics
  · exact fixed_host_0690_semantics
  · exact fixed_host_0691_semantics
  · exact fixed_host_0692_semantics
  · exact fixed_host_0693_semantics
  · exact fixed_host_0694_semantics
  · exact fixed_host_0695_semantics

end InducedPentagons.Paper

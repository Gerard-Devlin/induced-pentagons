import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData059
import InducedPentagonsPaper.Generated.FixedRows051

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0708 :
    (fixedDensityCounts (maskGraph 7 48825), fixedComplementCounts (maskGraph 7 48825)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 4, 1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0708_semantics :
    ((Generated.hostChunk059[0]).induced.toList, (Generated.hostChunk059[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[0]).mask)) := by
  have hm : (Generated.hostChunk059[0]).mask = 48825 := by decide +kernel
  have hv : ((Generated.hostChunk059[0]).induced.toList, (Generated.hostChunk059[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 4, 1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0708]

theorem fixed_values_0709 :
    (fixedDensityCounts (maskGraph 7 48826), fixedComplementCounts (maskGraph 7 48826)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 2, 3, 0, 0, 3, 3, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0709_semantics :
    ((Generated.hostChunk059[1]).induced.toList, (Generated.hostChunk059[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[1]).mask)) := by
  have hm : (Generated.hostChunk059[1]).mask = 48826 := by decide +kernel
  have hv : ((Generated.hostChunk059[1]).induced.toList, (Generated.hostChunk059[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 2, 3, 0, 0, 3, 3, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0709]

theorem fixed_values_0710 :
    (fixedDensityCounts (maskGraph 7 48827), fixedComplementCounts (maskGraph 7 48827)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 1, 1, 3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 4, 3, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0710_semantics :
    ((Generated.hostChunk059[2]).induced.toList, (Generated.hostChunk059[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[2]).mask)) := by
  have hm : (Generated.hostChunk059[2]).mask = 48827 := by decide +kernel
  have hv : ((Generated.hostChunk059[2]).induced.toList, (Generated.hostChunk059[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 1, 1, 3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 4, 3, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0710]

theorem fixed_values_0711 :
    (fixedDensityCounts (maskGraph 7 48828), fixedComplementCounts (maskGraph 7 48828)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 0, 7, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0711_semantics :
    ((Generated.hostChunk059[3]).induced.toList, (Generated.hostChunk059[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[3]).mask)) := by
  have hm : (Generated.hostChunk059[3]).mask = 48828 := by decide +kernel
  have hv : ((Generated.hostChunk059[3]).induced.toList, (Generated.hostChunk059[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 0, 7, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0711]

theorem fixed_values_0712 :
    (fixedDensityCounts (maskGraph 7 48829), fixedComplementCounts (maskGraph 7 48829)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 3, 1, 0, 1, 0, 0, 2, 3, 0, 0, 0, 2, 3, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0712_semantics :
    ((Generated.hostChunk059[4]).induced.toList, (Generated.hostChunk059[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[4]).mask)) := by
  have hm : (Generated.hostChunk059[4]).mask = 48829 := by decide +kernel
  have hv : ((Generated.hostChunk059[4]).induced.toList, (Generated.hostChunk059[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 3, 1, 0, 1, 0, 0, 2, 3, 0, 0, 0, 2, 3, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0712]

theorem fixed_values_0713 :
    (fixedDensityCounts (maskGraph 7 48830), fixedComplementCounts (maskGraph 7 48830)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 2, 1, 2, 0, 0, 5, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0713_semantics :
    ((Generated.hostChunk059[5]).induced.toList, (Generated.hostChunk059[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[5]).mask)) := by
  have hm : (Generated.hostChunk059[5]).mask = 48830 := by decide +kernel
  have hv : ((Generated.hostChunk059[5]).induced.toList, (Generated.hostChunk059[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 2, 1, 2, 0, 0, 5, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0713]

theorem fixed_values_0714 :
    (fixedDensityCounts (maskGraph 7 48831), fixedComplementCounts (maskGraph 7 48831)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 3, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 5, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0714_semantics :
    ((Generated.hostChunk059[6]).induced.toList, (Generated.hostChunk059[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[6]).mask)) := by
  have hm : (Generated.hostChunk059[6]).mask = 48831 := by decide +kernel
  have hv : ((Generated.hostChunk059[6]).induced.toList, (Generated.hostChunk059[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 3, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 5, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0714]

theorem fixed_values_0715 :
    (fixedDensityCounts (maskGraph 7 48886), fixedComplementCounts (maskGraph 7 48886)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 3, 3, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0715_semantics :
    ((Generated.hostChunk059[7]).induced.toList, (Generated.hostChunk059[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[7]).mask)) := by
  have hm : (Generated.hostChunk059[7]).mask = 48886 := by decide +kernel
  have hv : ((Generated.hostChunk059[7]).induced.toList, (Generated.hostChunk059[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 3, 3, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0715]

theorem fixed_values_0716 :
    (fixedDensityCounts (maskGraph 7 48887), fixedComplementCounts (maskGraph 7 48887)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 5, 1, 0, 0, 0, 2, 0, 3, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0716_semantics :
    ((Generated.hostChunk059[8]).induced.toList, (Generated.hostChunk059[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[8]).mask)) := by
  have hm : (Generated.hostChunk059[8]).mask = 48887 := by decide +kernel
  have hv : ((Generated.hostChunk059[8]).induced.toList, (Generated.hostChunk059[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 0, 0, 5, 1, 0, 0, 0, 2, 0, 3, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0716]

theorem fixed_values_0717 :
    (fixedDensityCounts (maskGraph 7 48890), fixedComplementCounts (maskGraph 7 48890)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 5, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0717_semantics :
    ((Generated.hostChunk059[9]).induced.toList, (Generated.hostChunk059[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[9]).mask)) := by
  have hm : (Generated.hostChunk059[9]).mask = 48890 := by decide +kernel
  have hv : ((Generated.hostChunk059[9]).induced.toList, (Generated.hostChunk059[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 5, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0717]

theorem fixed_values_0718 :
    (fixedDensityCounts (maskGraph 7 48891), fixedComplementCounts (maskGraph 7 48891)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 4, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0718_semantics :
    ((Generated.hostChunk059[10]).induced.toList, (Generated.hostChunk059[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[10]).mask)) := by
  have hm : (Generated.hostChunk059[10]).mask = 48891 := by decide +kernel
  have hv : ((Generated.hostChunk059[10]).induced.toList, (Generated.hostChunk059[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 4, 0, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0718]

theorem fixed_values_0719 :
    (fixedDensityCounts (maskGraph 7 48892), fixedComplementCounts (maskGraph 7 48892)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 2, 0, 0, 1, 5, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0719_semantics :
    ((Generated.hostChunk059[11]).induced.toList, (Generated.hostChunk059[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk059[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk059[11]).mask)) := by
  have hm : (Generated.hostChunk059[11]).mask = 48892 := by decide +kernel
  have hv : ((Generated.hostChunk059[11]).induced.toList, (Generated.hostChunk059[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0, 2, 0, 0, 1, 5, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0719]

theorem fixed_chunk_059_semantics :
    ∀ h ∈ Generated.hostChunk059.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk059.toList = [Generated.hostChunk059[0], Generated.hostChunk059[1], Generated.hostChunk059[2], Generated.hostChunk059[3], Generated.hostChunk059[4], Generated.hostChunk059[5], Generated.hostChunk059[6], Generated.hostChunk059[7], Generated.hostChunk059[8], Generated.hostChunk059[9], Generated.hostChunk059[10], Generated.hostChunk059[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0708_semantics
  · exact fixed_host_0709_semantics
  · exact fixed_host_0710_semantics
  · exact fixed_host_0711_semantics
  · exact fixed_host_0712_semantics
  · exact fixed_host_0713_semantics
  · exact fixed_host_0714_semantics
  · exact fixed_host_0715_semantics
  · exact fixed_host_0716_semantics
  · exact fixed_host_0717_semantics
  · exact fixed_host_0718_semantics
  · exact fixed_host_0719_semantics

end InducedPentagons.Paper

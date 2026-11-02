import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData076
import InducedPentagonsPaper.Generated.FixedRows068

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0912 :
    (fixedDensityCounts (maskGraph 7 122878), fixedComplementCounts (maskGraph 7 122878)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 4, 4, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0912_semantics :
    ((Generated.hostChunk076[0]).induced.toList, (Generated.hostChunk076[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[0]).mask)) := by
  have hm : (Generated.hostChunk076[0]).mask = 122878 := by decide +kernel
  have hv : ((Generated.hostChunk076[0]).induced.toList, (Generated.hostChunk076[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 4, 4, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0912]

theorem fixed_values_0913 :
    (fixedDensityCounts (maskGraph 7 122879), fixedComplementCounts (maskGraph 7 122879)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 4, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0913_semantics :
    ((Generated.hostChunk076[1]).induced.toList, (Generated.hostChunk076[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[1]).mask)) := by
  have hm : (Generated.hostChunk076[1]).mask = 122879 := by decide +kernel
  have hv : ((Generated.hostChunk076[1]).induced.toList, (Generated.hostChunk076[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 4, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0913]

theorem fixed_values_0914 :
    (fixedDensityCounts (maskGraph 7 128831), fixedComplementCounts (maskGraph 7 128831)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0]) := by
  decide +kernel

theorem fixed_host_0914_semantics :
    ((Generated.hostChunk076[2]).induced.toList, (Generated.hostChunk076[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[2]).mask)) := by
  have hm : (Generated.hostChunk076[2]).mask = 128831 := by decide +kernel
  have hv : ((Generated.hostChunk076[2]).induced.toList, (Generated.hostChunk076[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0914]

theorem fixed_values_0915 :
    (fixedDensityCounts (maskGraph 7 128891), fixedComplementCounts (maskGraph 7 128891)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 1, 0, 0, 6, 2, 0, 0, 0, 0, 3, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0915_semantics :
    ((Generated.hostChunk076[3]).induced.toList, (Generated.hostChunk076[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[3]).mask)) := by
  have hm : (Generated.hostChunk076[3]).mask = 128891 := by decide +kernel
  have hv : ((Generated.hostChunk076[3]).induced.toList, (Generated.hostChunk076[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 1, 0, 0, 6, 2, 0, 0, 0, 0, 3, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0915]

theorem fixed_values_0916 :
    (fixedDensityCounts (maskGraph 7 128892), fixedComplementCounts (maskGraph 7 128892)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 1, 2, 0, 2, 0, 4, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0916_semantics :
    ((Generated.hostChunk076[4]).induced.toList, (Generated.hostChunk076[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[4]).mask)) := by
  have hm : (Generated.hostChunk076[4]).mask = 128892 := by decide +kernel
  have hv : ((Generated.hostChunk076[4]).induced.toList, (Generated.hostChunk076[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 1, 2, 0, 2, 0, 4, 0, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0916]

theorem fixed_values_0917 :
    (fixedDensityCounts (maskGraph 7 128893), fixedComplementCounts (maskGraph 7 128893)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0, 0, 3, 0, 0, 0, 2, 4, 2, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 3, 0, 0]) := by
  decide +kernel

theorem fixed_host_0917_semantics :
    ((Generated.hostChunk076[5]).induced.toList, (Generated.hostChunk076[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[5]).mask)) := by
  have hm : (Generated.hostChunk076[5]).mask = 128893 := by decide +kernel
  have hv : ((Generated.hostChunk076[5]).induced.toList, (Generated.hostChunk076[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 2, 0, 0, 0, 3, 0, 0, 0, 2, 4, 2, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 3, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0917]

theorem fixed_values_0918 :
    (fixedDensityCounts (maskGraph 7 128895), fixedComplementCounts (maskGraph 7 128895)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 0, 0, 0, 2, 1, 0, 0, 0, 4, 1, 2, 2, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 4, 1, 0, 2, 2, 0]) := by
  decide +kernel

theorem fixed_host_0918_semantics :
    ((Generated.hostChunk076[6]).induced.toList, (Generated.hostChunk076[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[6]).mask)) := by
  have hm : (Generated.hostChunk076[6]).mask = 128895 := by decide +kernel
  have hv : ((Generated.hostChunk076[6]).induced.toList, (Generated.hostChunk076[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 0, 0, 0, 2, 1, 0, 0, 0, 4, 1, 2, 2, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 4, 1, 0, 2, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0918]

theorem fixed_values_0919 :
    (fixedDensityCounts (maskGraph 7 128956), fixedComplementCounts (maskGraph 7 128956)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0919_semantics :
    ((Generated.hostChunk076[7]).induced.toList, (Generated.hostChunk076[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[7]).mask)) := by
  have hm : (Generated.hostChunk076[7]).mask = 128956 := by decide +kernel
  have hv : ((Generated.hostChunk076[7]).induced.toList, (Generated.hostChunk076[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0919]

theorem fixed_values_0920 :
    (fixedDensityCounts (maskGraph 7 128957), fixedComplementCounts (maskGraph 7 128957)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 1, 2, 0, 0, 4, 0, 5, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0920_semantics :
    ((Generated.hostChunk076[8]).induced.toList, (Generated.hostChunk076[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[8]).mask)) := by
  have hm : (Generated.hostChunk076[8]).mask = 128957 := by decide +kernel
  have hv : ((Generated.hostChunk076[8]).induced.toList, (Generated.hostChunk076[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 1, 2, 0, 0, 4, 0, 5, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0920]

theorem fixed_values_0921 :
    (fixedDensityCounts (maskGraph 7 128958), fixedComplementCounts (maskGraph 7 128958)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 3, 4, 6, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 5, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0921_semantics :
    ((Generated.hostChunk076[9]).induced.toList, (Generated.hostChunk076[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[9]).mask)) := by
  have hm : (Generated.hostChunk076[9]).mask = 128958 := by decide +kernel
  have hv : ((Generated.hostChunk076[9]).induced.toList, (Generated.hostChunk076[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 3, 4, 6, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 5, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0921]

theorem fixed_values_0922 :
    (fixedDensityCounts (maskGraph 7 128959), fixedComplementCounts (maskGraph 7 128959)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 4, 4, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 3, 1, 0]) := by
  decide +kernel

theorem fixed_host_0922_semantics :
    ((Generated.hostChunk076[10]).induced.toList, (Generated.hostChunk076[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[10]).mask)) := by
  have hm : (Generated.hostChunk076[10]).mask = 128959 := by decide +kernel
  have hv : ((Generated.hostChunk076[10]).induced.toList, (Generated.hostChunk076[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 4, 4, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 3, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0922]

theorem fixed_values_0923 :
    (fixedDensityCounts (maskGraph 7 129022), fixedComplementCounts (maskGraph 7 129022)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 8, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 5, 0, 0]) := by
  decide +kernel

theorem fixed_host_0923_semantics :
    ((Generated.hostChunk076[11]).induced.toList, (Generated.hostChunk076[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk076[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk076[11]).mask)) := by
  have hm : (Generated.hostChunk076[11]).mask = 129022 := by decide +kernel
  have hv : ((Generated.hostChunk076[11]).induced.toList, (Generated.hostChunk076[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 8, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 5, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0923]

theorem fixed_chunk_076_semantics :
    ∀ h ∈ Generated.hostChunk076.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk076.toList = [Generated.hostChunk076[0], Generated.hostChunk076[1], Generated.hostChunk076[2], Generated.hostChunk076[3], Generated.hostChunk076[4], Generated.hostChunk076[5], Generated.hostChunk076[6], Generated.hostChunk076[7], Generated.hostChunk076[8], Generated.hostChunk076[9], Generated.hostChunk076[10], Generated.hostChunk076[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0912_semantics
  · exact fixed_host_0913_semantics
  · exact fixed_host_0914_semantics
  · exact fixed_host_0915_semantics
  · exact fixed_host_0916_semantics
  · exact fixed_host_0917_semantics
  · exact fixed_host_0918_semantics
  · exact fixed_host_0919_semantics
  · exact fixed_host_0920_semantics
  · exact fixed_host_0921_semantics
  · exact fixed_host_0922_semantics
  · exact fixed_host_0923_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData074
import InducedPentagonsPaper.Generated.FixedRows066

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0888 :
    (fixedDensityCounts (maskGraph 7 120575), fixedComplementCounts (maskGraph 7 120575)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 4, 0, 6, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 4, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0888_semantics :
    ((Generated.hostChunk074[0]).induced.toList, (Generated.hostChunk074[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[0]).mask)) := by
  have hm : (Generated.hostChunk074[0]).mask = 120575 := by decide +kernel
  have hv : ((Generated.hostChunk074[0]).induced.toList, (Generated.hostChunk074[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 4, 0, 6, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 4, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0888]

theorem fixed_values_0889 :
    (fixedDensityCounts (maskGraph 7 120639), fixedComplementCounts (maskGraph 7 120639)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0889_semantics :
    ((Generated.hostChunk074[1]).induced.toList, (Generated.hostChunk074[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[1]).mask)) := by
  have hm : (Generated.hostChunk074[1]).mask = 120639 := by decide +kernel
  have hv : ((Generated.hostChunk074[1]).induced.toList, (Generated.hostChunk074[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 4, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0889]

theorem fixed_values_0890 :
    (fixedDensityCounts (maskGraph 7 120699), fixedComplementCounts (maskGraph 7 120699)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 5, 1, 0, 0, 2, 0, 1, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 2, 0, 1, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0890_semantics :
    ((Generated.hostChunk074[2]).induced.toList, (Generated.hostChunk074[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[2]).mask)) := by
  have hm : (Generated.hostChunk074[2]).mask = 120699 := by decide +kernel
  have hv : ((Generated.hostChunk074[2]).induced.toList, (Generated.hostChunk074[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 5, 1, 0, 0, 2, 0, 1, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 2, 0, 1, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0890]

theorem fixed_values_0891 :
    (fixedDensityCounts (maskGraph 7 120700), fixedComplementCounts (maskGraph 7 120700)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 4, 2, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0891_semantics :
    ((Generated.hostChunk074[3]).induced.toList, (Generated.hostChunk074[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[3]).mask)) := by
  have hm : (Generated.hostChunk074[3]).mask = 120700 := by decide +kernel
  have hv : ((Generated.hostChunk074[3]).induced.toList, (Generated.hostChunk074[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0, 4, 2, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0891]

theorem fixed_values_0892 :
    (fixedDensityCounts (maskGraph 7 120701), fixedComplementCounts (maskGraph 7 120701)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 1, 0, 0, 2, 4, 0, 0, 0, 2, 5, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0892_semantics :
    ((Generated.hostChunk074[4]).induced.toList, (Generated.hostChunk074[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[4]).mask)) := by
  have hm : (Generated.hostChunk074[4]).mask = 120701 := by decide +kernel
  have hv : ((Generated.hostChunk074[4]).induced.toList, (Generated.hostChunk074[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 1, 0, 0, 2, 4, 0, 0, 0, 2, 5, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0892]

theorem fixed_values_0893 :
    (fixedDensityCounts (maskGraph 7 120702), fixedComplementCounts (maskGraph 7 120702)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 1, 0, 0, 0, 1, 2, 0, 1, 0, 4, 3, 3, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 2, 2, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0893_semantics :
    ((Generated.hostChunk074[5]).induced.toList, (Generated.hostChunk074[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[5]).mask)) := by
  have hm : (Generated.hostChunk074[5]).mask = 120702 := by decide +kernel
  have hv : ((Generated.hostChunk074[5]).induced.toList, (Generated.hostChunk074[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 1, 0, 0, 0, 1, 2, 0, 1, 0, 4, 3, 3, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 2, 2, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0893]

theorem fixed_values_0894 :
    (fixedDensityCounts (maskGraph 7 120703), fixedComplementCounts (maskGraph 7 120703)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 5, 0, 3, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 3, 0, 1, 1, 1, 0]) := by
  decide +kernel

theorem fixed_host_0894_semantics :
    ((Generated.hostChunk074[6]).induced.toList, (Generated.hostChunk074[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[6]).mask)) := by
  have hm : (Generated.hostChunk074[6]).mask = 120703 := by decide +kernel
  have hv : ((Generated.hostChunk074[6]).induced.toList, (Generated.hostChunk074[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 5, 0, 3, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 3, 0, 1, 1, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0894]

theorem fixed_values_0895 :
    (fixedDensityCounts (maskGraph 7 120830), fixedComplementCounts (maskGraph 7 120830)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 6, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 2, 0, 2, 0, 0]) := by
  decide +kernel

theorem fixed_host_0895_semantics :
    ((Generated.hostChunk074[7]).induced.toList, (Generated.hostChunk074[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[7]).mask)) := by
  have hm : (Generated.hostChunk074[7]).mask = 120830 := by decide +kernel
  have hv : ((Generated.hostChunk074[7]).induced.toList, (Generated.hostChunk074[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 6, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 2, 0, 2, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0895]

theorem fixed_values_0896 :
    (fixedDensityCounts (maskGraph 7 120831), fixedComplementCounts (maskGraph 7 120831)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 6, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 2, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0896_semantics :
    ((Generated.hostChunk074[8]).induced.toList, (Generated.hostChunk074[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[8]).mask)) := by
  have hm : (Generated.hostChunk074[8]).mask = 120831 := by decide +kernel
  have hv : ((Generated.hostChunk074[8]).induced.toList, (Generated.hostChunk074[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 6, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 2, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0896]

theorem fixed_values_0897 :
    (fixedDensityCounts (maskGraph 7 122616), fixedComplementCounts (maskGraph 7 122616)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 6, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0897_semantics :
    ((Generated.hostChunk074[9]).induced.toList, (Generated.hostChunk074[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[9]).mask)) := by
  have hm : (Generated.hostChunk074[9]).mask = 122616 := by decide +kernel
  have hv : ((Generated.hostChunk074[9]).induced.toList, (Generated.hostChunk074[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 6, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0897]

theorem fixed_values_0898 :
    (fixedDensityCounts (maskGraph 7 122617), fixedComplementCounts (maskGraph 7 122617)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 7, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0898_semantics :
    ((Generated.hostChunk074[10]).induced.toList, (Generated.hostChunk074[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[10]).mask)) := by
  have hm : (Generated.hostChunk074[10]).mask = 122617 := by decide +kernel
  have hv : ((Generated.hostChunk074[10]).induced.toList, (Generated.hostChunk074[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 7, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0898]

theorem fixed_values_0899 :
    (fixedDensityCounts (maskGraph 7 122619), fixedComplementCounts (maskGraph 7 122619)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 3, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0899_semantics :
    ((Generated.hostChunk074[11]).induced.toList, (Generated.hostChunk074[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk074[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk074[11]).mask)) := by
  have hm : (Generated.hostChunk074[11]).mask = 122619 := by decide +kernel
  have hv : ((Generated.hostChunk074[11]).induced.toList, (Generated.hostChunk074[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 3, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0899]

theorem fixed_chunk_074_semantics :
    ∀ h ∈ Generated.hostChunk074.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk074.toList = [Generated.hostChunk074[0], Generated.hostChunk074[1], Generated.hostChunk074[2], Generated.hostChunk074[3], Generated.hostChunk074[4], Generated.hostChunk074[5], Generated.hostChunk074[6], Generated.hostChunk074[7], Generated.hostChunk074[8], Generated.hostChunk074[9], Generated.hostChunk074[10], Generated.hostChunk074[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0888_semantics
  · exact fixed_host_0889_semantics
  · exact fixed_host_0890_semantics
  · exact fixed_host_0891_semantics
  · exact fixed_host_0892_semantics
  · exact fixed_host_0893_semantics
  · exact fixed_host_0894_semantics
  · exact fixed_host_0895_semantics
  · exact fixed_host_0896_semantics
  · exact fixed_host_0897_semantics
  · exact fixed_host_0898_semantics
  · exact fixed_host_0899_semantics

end InducedPentagons.Paper

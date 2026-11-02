import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData081
import InducedPentagonsPaper.Generated.FixedRows073

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0972 :
    (fixedDensityCounts (maskGraph 7 376830), fixedComplementCounts (maskGraph 7 376830)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 6, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 6, 0, 0, 0, 2]) := by
  decide +kernel

theorem fixed_host_0972_semantics :
    ((Generated.hostChunk081[0]).induced.toList, (Generated.hostChunk081[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[0]).mask)) := by
  have hm : (Generated.hostChunk081[0]).mask = 376830 := by decide +kernel
  have hv : ((Generated.hostChunk081[0]).induced.toList, (Generated.hostChunk081[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 6, 0, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 6, 0, 0, 0, 2]) := by decide +kernel
  rw [hm, hv, fixed_values_0972]

theorem fixed_values_0973 :
    (fixedDensityCounts (maskGraph 7 376831), fixedComplementCounts (maskGraph 7 376831)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 2]) := by
  decide +kernel

theorem fixed_host_0973_semantics :
    ((Generated.hostChunk081[1]).induced.toList, (Generated.hostChunk081[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[1]).mask)) := by
  have hm : (Generated.hostChunk081[1]).mask = 376831 := by decide +kernel
  have hv : ((Generated.hostChunk081[1]).induced.toList, (Generated.hostChunk081[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 6], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 2]) := by decide +kernel
  rw [hm, hv, fixed_values_0973]

theorem fixed_values_0974 :
    (fixedDensityCounts (maskGraph 7 377983), fixedComplementCounts (maskGraph 7 377983)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0974_semantics :
    ((Generated.hostChunk081[2]).induced.toList, (Generated.hostChunk081[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[2]).mask)) := by
  have hm : (Generated.hostChunk081[2]).mask = 377983 := by decide +kernel
  have hv : ((Generated.hostChunk081[2]).induced.toList, (Generated.hostChunk081[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0974]

theorem fixed_values_0975 :
    (fixedDensityCounts (maskGraph 7 378106), fixedComplementCounts (maskGraph 7 378106)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 6, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0975_semantics :
    ((Generated.hostChunk081[3]).induced.toList, (Generated.hostChunk081[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[3]).mask)) := by
  have hm : (Generated.hostChunk081[3]).mask = 378106 := by decide +kernel
  have hv : ((Generated.hostChunk081[3]).induced.toList, (Generated.hostChunk081[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 6, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0975]

theorem fixed_values_0976 :
    (fixedDensityCounts (maskGraph 7 378107), fixedComplementCounts (maskGraph 7 378107)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 3, 3, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0976_semantics :
    ((Generated.hostChunk081[4]).induced.toList, (Generated.hostChunk081[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[4]).mask)) := by
  have hm : (Generated.hostChunk081[4]).mask = 378107 := by decide +kernel
  have hv : ((Generated.hostChunk081[4]).induced.toList, (Generated.hostChunk081[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 3, 3, 0, 4, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0976]

theorem fixed_values_0977 :
    (fixedDensityCounts (maskGraph 7 378111), fixedComplementCounts (maskGraph 7 378111)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 5, 0, 0, 4, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 1, 0, 0, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0977_semantics :
    ((Generated.hostChunk081[5]).induced.toList, (Generated.hostChunk081[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[5]).mask)) := by
  have hm : (Generated.hostChunk081[5]).mask = 378111 := by decide +kernel
  have hv : ((Generated.hostChunk081[5]).induced.toList, (Generated.hostChunk081[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 5, 0, 0, 4, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 4, 1, 0, 0, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0977]

theorem fixed_values_0978 :
    (fixedDensityCounts (maskGraph 7 378358), fixedComplementCounts (maskGraph 7 378358)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 6, 0, 2, 2, 4, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0978_semantics :
    ((Generated.hostChunk081[6]).induced.toList, (Generated.hostChunk081[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[6]).mask)) := by
  have hm : (Generated.hostChunk081[6]).mask = 378358 := by decide +kernel
  have hv : ((Generated.hostChunk081[6]).induced.toList, (Generated.hostChunk081[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 6, 0, 2, 2, 4, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0978]

theorem fixed_values_0979 :
    (fixedDensityCounts (maskGraph 7 378359), fixedComplementCounts (maskGraph 7 378359)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 2, 2, 0, 2, 4, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0979_semantics :
    ((Generated.hostChunk081[7]).induced.toList, (Generated.hostChunk081[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[7]).mask)) := by
  have hm : (Generated.hostChunk081[7]).mask = 378359 := by decide +kernel
  have hv : ((Generated.hostChunk081[7]).induced.toList, (Generated.hostChunk081[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 2, 2, 0, 2, 4, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0979]

theorem fixed_values_0980 :
    (fixedDensityCounts (maskGraph 7 378366), fixedComplementCounts (maskGraph 7 378366)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 4, 0, 4, 0, 4, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 3, 0, 0, 0, 2, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0980_semantics :
    ((Generated.hostChunk081[8]).induced.toList, (Generated.hostChunk081[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[8]).mask)) := by
  have hm : (Generated.hostChunk081[8]).mask = 378366 := by decide +kernel
  have hv : ((Generated.hostChunk081[8]).induced.toList, (Generated.hostChunk081[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 4, 0, 4, 0, 4, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 3, 0, 0, 0, 2, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0980]

theorem fixed_values_0981 :
    (fixedDensityCounts (maskGraph 7 378367), fixedComplementCounts (maskGraph 7 378367)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 4, 0, 0, 4, 0, 4, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 3, 0, 0, 0, 0, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0981_semantics :
    ((Generated.hostChunk081[9]).induced.toList, (Generated.hostChunk081[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[9]).mask)) := by
  have hm : (Generated.hostChunk081[9]).mask = 378367 := by decide +kernel
  have hv : ((Generated.hostChunk081[9]).induced.toList, (Generated.hostChunk081[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 4, 0, 0, 4, 0, 4, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 3, 0, 0, 0, 0, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0981]

theorem fixed_values_0982 :
    (fixedDensityCounts (maskGraph 7 378878), fixedComplementCounts (maskGraph 7 378878)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 6, 0, 0, 0, 9, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 0, 0, 0, 3, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0982_semantics :
    ((Generated.hostChunk081[10]).induced.toList, (Generated.hostChunk081[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[10]).mask)) := by
  have hm : (Generated.hostChunk081[10]).mask = 378878 := by decide +kernel
  have hv : ((Generated.hostChunk081[10]).induced.toList, (Generated.hostChunk081[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 6, 0, 0, 0, 9, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 0, 0, 0, 3, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0982]

theorem fixed_values_0983 :
    (fixedDensityCounts (maskGraph 7 378879), fixedComplementCounts (maskGraph 7 378879)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 6, 0, 0, 0, 0, 9, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 6, 0, 0, 0, 0, 3, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0983_semantics :
    ((Generated.hostChunk081[11]).induced.toList, (Generated.hostChunk081[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk081[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk081[11]).mask)) := by
  have hm : (Generated.hostChunk081[11]).mask = 378879 := by decide +kernel
  have hv : ((Generated.hostChunk081[11]).induced.toList, (Generated.hostChunk081[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 6, 0, 0, 0, 0, 9, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 6, 0, 0, 0, 0, 3, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0983]

theorem fixed_chunk_081_semantics :
    ∀ h ∈ Generated.hostChunk081.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk081.toList = [Generated.hostChunk081[0], Generated.hostChunk081[1], Generated.hostChunk081[2], Generated.hostChunk081[3], Generated.hostChunk081[4], Generated.hostChunk081[5], Generated.hostChunk081[6], Generated.hostChunk081[7], Generated.hostChunk081[8], Generated.hostChunk081[9], Generated.hostChunk081[10], Generated.hostChunk081[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0972_semantics
  · exact fixed_host_0973_semantics
  · exact fixed_host_0974_semantics
  · exact fixed_host_0975_semantics
  · exact fixed_host_0976_semantics
  · exact fixed_host_0977_semantics
  · exact fixed_host_0978_semantics
  · exact fixed_host_0979_semantics
  · exact fixed_host_0980_semantics
  · exact fixed_host_0981_semantics
  · exact fixed_host_0982_semantics
  · exact fixed_host_0983_semantics

end InducedPentagons.Paper

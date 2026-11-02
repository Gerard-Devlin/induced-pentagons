import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData060
import InducedPentagonsPaper.Generated.FixedRows052

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0720 :
    (fixedDensityCounts (maskGraph 7 48893), fixedComplementCounts (maskGraph 7 48893)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 5, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0720_semantics :
    ((Generated.hostChunk060[0]).induced.toList, (Generated.hostChunk060[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[0]).mask)) := by
  have hm : (Generated.hostChunk060[0]).mask = 48893 := by decide +kernel
  have hv : ((Generated.hostChunk060[0]).induced.toList, (Generated.hostChunk060[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 2, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 5, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0720]

theorem fixed_values_0721 :
    (fixedDensityCounts (maskGraph 7 48894), fixedComplementCounts (maskGraph 7 48894)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 3, 2, 2, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0721_semantics :
    ((Generated.hostChunk060[1]).induced.toList, (Generated.hostChunk060[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[1]).mask)) := by
  have hm : (Generated.hostChunk060[1]).mask = 48894 := by decide +kernel
  have hv : ((Generated.hostChunk060[1]).induced.toList, (Generated.hostChunk060[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 3, 2, 2, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0721]

theorem fixed_values_0722 :
    (fixedDensityCounts (maskGraph 7 48895), fixedComplementCounts (maskGraph 7 48895)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 4, 0, 4, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0722_semantics :
    ((Generated.hostChunk060[2]).induced.toList, (Generated.hostChunk060[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[2]).mask)) := by
  have hm : (Generated.hostChunk060[2]).mask = 48895 := by decide +kernel
  have hv : ((Generated.hostChunk060[2]).induced.toList, (Generated.hostChunk060[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 4, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 4, 0, 4, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0722]

theorem fixed_values_0723 :
    (fixedDensityCounts (maskGraph 7 49084), fixedComplementCounts (maskGraph 7 49084)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 7, 0, 4, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0723_semantics :
    ((Generated.hostChunk060[3]).induced.toList, (Generated.hostChunk060[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[3]).mask)) := by
  have hm : (Generated.hostChunk060[3]).mask = 49084 := by decide +kernel
  have hv : ((Generated.hostChunk060[3]).induced.toList, (Generated.hostChunk060[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 7, 0, 4, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0723]

theorem fixed_values_0724 :
    (fixedDensityCounts (maskGraph 7 49085), fixedComplementCounts (maskGraph 7 49085)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0724_semantics :
    ((Generated.hostChunk060[4]).induced.toList, (Generated.hostChunk060[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[4]).mask)) := by
  have hm : (Generated.hostChunk060[4]).mask = 49085 := by decide +kernel
  have hv : ((Generated.hostChunk060[4]).induced.toList, (Generated.hostChunk060[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0724]

theorem fixed_values_0725 :
    (fixedDensityCounts (maskGraph 7 49086), fixedComplementCounts (maskGraph 7 49086)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 5, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 2, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0725_semantics :
    ((Generated.hostChunk060[5]).induced.toList, (Generated.hostChunk060[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[5]).mask)) := by
  have hm : (Generated.hostChunk060[5]).mask = 49086 := by decide +kernel
  have hv : ((Generated.hostChunk060[5]).induced.toList, (Generated.hostChunk060[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 5, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 2, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0725]

theorem fixed_values_0726 :
    (fixedDensityCounts (maskGraph 7 49087), fixedComplementCounts (maskGraph 7 49087)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 3, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0726_semantics :
    ((Generated.hostChunk060[6]).induced.toList, (Generated.hostChunk060[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[6]).mask)) := by
  have hm : (Generated.hostChunk060[6]).mask = 49087 := by decide +kernel
  have hv : ((Generated.hostChunk060[6]).induced.toList, (Generated.hostChunk060[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 3, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0726]

theorem fixed_values_0727 :
    (fixedDensityCounts (maskGraph 7 49150), fixedComplementCounts (maskGraph 7 49150)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 5, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0727_semantics :
    ((Generated.hostChunk060[7]).induced.toList, (Generated.hostChunk060[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[7]).mask)) := by
  have hm : (Generated.hostChunk060[7]).mask = 49150 := by decide +kernel
  have hv : ((Generated.hostChunk060[7]).induced.toList, (Generated.hostChunk060[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 5, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0727]

theorem fixed_values_0728 :
    (fixedDensityCounts (maskGraph 7 49151), fixedComplementCounts (maskGraph 7 49151)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 7, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0728_semantics :
    ((Generated.hostChunk060[8]).induced.toList, (Generated.hostChunk060[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[8]).mask)) := by
  have hm : (Generated.hostChunk060[8]).mask = 49151 := by decide +kernel
  have hv : ((Generated.hostChunk060[8]).induced.toList, (Generated.hostChunk060[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 7, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0728]

theorem fixed_values_0729 :
    (fixedDensityCounts (maskGraph 7 58931), fixedComplementCounts (maskGraph 7 58931)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 2, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0729_semantics :
    ((Generated.hostChunk060[9]).induced.toList, (Generated.hostChunk060[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[9]).mask)) := by
  have hm : (Generated.hostChunk060[9]).mask = 58931 := by decide +kernel
  have hv : ((Generated.hostChunk060[9]).induced.toList, (Generated.hostChunk060[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 2, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0729]

theorem fixed_values_0730 :
    (fixedDensityCounts (maskGraph 7 58935), fixedComplementCounts (maskGraph 7 58935)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 2, 4, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0730_semantics :
    ((Generated.hostChunk060[10]).induced.toList, (Generated.hostChunk060[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[10]).mask)) := by
  have hm : (Generated.hostChunk060[10]).mask = 58935 := by decide +kernel
  have hv : ((Generated.hostChunk060[10]).induced.toList, (Generated.hostChunk060[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 2, 4, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0730]

theorem fixed_values_0731 :
    (fixedDensityCounts (maskGraph 7 58943), fixedComplementCounts (maskGraph 7 58943)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 2, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0731_semantics :
    ((Generated.hostChunk060[11]).induced.toList, (Generated.hostChunk060[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk060[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk060[11]).mask)) := by
  have hm : (Generated.hostChunk060[11]).mask = 58943 := by decide +kernel
  have hv : ((Generated.hostChunk060[11]).induced.toList, (Generated.hostChunk060[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 2, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0731]

theorem fixed_chunk_060_semantics :
    ∀ h ∈ Generated.hostChunk060.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk060.toList = [Generated.hostChunk060[0], Generated.hostChunk060[1], Generated.hostChunk060[2], Generated.hostChunk060[3], Generated.hostChunk060[4], Generated.hostChunk060[5], Generated.hostChunk060[6], Generated.hostChunk060[7], Generated.hostChunk060[8], Generated.hostChunk060[9], Generated.hostChunk060[10], Generated.hostChunk060[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0720_semantics
  · exact fixed_host_0721_semantics
  · exact fixed_host_0722_semantics
  · exact fixed_host_0723_semantics
  · exact fixed_host_0724_semantics
  · exact fixed_host_0725_semantics
  · exact fixed_host_0726_semantics
  · exact fixed_host_0727_semantics
  · exact fixed_host_0728_semantics
  · exact fixed_host_0729_semantics
  · exact fixed_host_0730_semantics
  · exact fixed_host_0731_semantics

end InducedPentagons.Paper

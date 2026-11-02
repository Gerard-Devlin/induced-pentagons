import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData082
import InducedPentagonsPaper.Generated.FixedRows074

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0984 :
    (fixedDensityCounts (maskGraph 7 380275), fixedComplementCounts (maskGraph 7 380275)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 3, 0, 0, 9, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 6, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0984_semantics :
    ((Generated.hostChunk082[0]).induced.toList, (Generated.hostChunk082[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[0]).mask)) := by
  have hm : (Generated.hostChunk082[0]).mask = 380275 := by decide +kernel
  have hv : ((Generated.hostChunk082[0]).induced.toList, (Generated.hostChunk082[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 3, 0, 0, 9, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 6, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0984]

theorem fixed_values_0985 :
    (fixedDensityCounts (maskGraph 7 380278), fixedComplementCounts (maskGraph 7 380278)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0985_semantics :
    ((Generated.hostChunk082[1]).induced.toList, (Generated.hostChunk082[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[1]).mask)) := by
  have hm : (Generated.hostChunk082[1]).mask = 380278 := by decide +kernel
  have hv : ((Generated.hostChunk082[1]).induced.toList, (Generated.hostChunk082[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 3, 3, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0985]

theorem fixed_values_0986 :
    (fixedDensityCounts (maskGraph 7 380279), fixedComplementCounts (maskGraph 7 380279)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 2, 1, 0, 5, 3, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 3, 2, 1, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0986_semantics :
    ((Generated.hostChunk082[2]).induced.toList, (Generated.hostChunk082[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[2]).mask)) := by
  have hm : (Generated.hostChunk082[2]).mask = 380279 := by decide +kernel
  have hv : ((Generated.hostChunk082[2]).induced.toList, (Generated.hostChunk082[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 2, 1, 0, 5, 3, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 3, 2, 1, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0986]

theorem fixed_values_0987 :
    (fixedDensityCounts (maskGraph 7 380287), fixedComplementCounts (maskGraph 7 380287)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 2, 0, 2, 6, 0, 4, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 2, 2, 0, 4, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0987_semantics :
    ((Generated.hostChunk082[3]).induced.toList, (Generated.hostChunk082[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[3]).mask)) := by
  have hm : (Generated.hostChunk082[3]).mask = 380287 := by decide +kernel
  have hv : ((Generated.hostChunk082[3]).induced.toList, (Generated.hostChunk082[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 2, 0, 2, 6, 0, 4, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 2, 2, 0, 4, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0987]

theorem fixed_values_0988 :
    (fixedDensityCounts (maskGraph 7 380406), fixedComplementCounts (maskGraph 7 380406)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 2, 2, 7, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 1, 0, 5, 0, 0, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0988_semantics :
    ((Generated.hostChunk082[4]).induced.toList, (Generated.hostChunk082[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[4]).mask)) := by
  have hm : (Generated.hostChunk082[4]).mask = 380406 := by decide +kernel
  have hv : ((Generated.hostChunk082[4]).induced.toList, (Generated.hostChunk082[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 2, 2, 7, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 1, 0, 5, 0, 0, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0988]

theorem fixed_values_0989 :
    (fixedDensityCounts (maskGraph 7 380407), fixedComplementCounts (maskGraph 7 380407)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 2, 0, 0, 2, 6, 0, 2, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 0, 0, 1, 4, 0, 0, 1, 1, 0]) := by
  decide +kernel

theorem fixed_host_0989_semantics :
    ((Generated.hostChunk082[5]).induced.toList, (Generated.hostChunk082[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[5]).mask)) := by
  have hm : (Generated.hostChunk082[5]).mask = 380407 := by decide +kernel
  have hv : ((Generated.hostChunk082[5]).induced.toList, (Generated.hostChunk082[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 2, 0, 0, 2, 6, 0, 2, 1, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 0, 0, 1, 4, 0, 0, 1, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0989]

theorem fixed_values_0990 :
    (fixedDensityCounts (maskGraph 7 380410), fixedComplementCounts (maskGraph 7 380410)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 1, 1, 6, 4, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 2, 4, 2, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0990_semantics :
    ((Generated.hostChunk082[6]).induced.toList, (Generated.hostChunk082[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[6]).mask)) := by
  have hm : (Generated.hostChunk082[6]).mask = 380410 := by decide +kernel
  have hv : ((Generated.hostChunk082[6]).induced.toList, (Generated.hostChunk082[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 1, 1, 6, 4, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 2, 4, 2, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0990]

theorem fixed_values_0991 :
    (fixedDensityCounts (maskGraph 7 380411), fixedComplementCounts (maskGraph 7 380411)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 1, 0, 3, 5, 2, 2, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 1, 0, 1, 3, 1, 2, 1, 0, 0]) := by
  decide +kernel

theorem fixed_host_0991_semantics :
    ((Generated.hostChunk082[7]).induced.toList, (Generated.hostChunk082[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[7]).mask)) := by
  have hm : (Generated.hostChunk082[7]).mask = 380411 := by decide +kernel
  have hv : ((Generated.hostChunk082[7]).induced.toList, (Generated.hostChunk082[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 1, 0, 3, 5, 2, 2, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 1, 0, 1, 3, 1, 2, 1, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0991]

theorem fixed_values_0992 :
    (fixedDensityCounts (maskGraph 7 380415), fixedComplementCounts (maskGraph 7 380415)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 7, 0, 4, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 4, 0, 2, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0992_semantics :
    ((Generated.hostChunk082[8]).induced.toList, (Generated.hostChunk082[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[8]).mask)) := by
  have hm : (Generated.hostChunk082[8]).mask = 380415 := by decide +kernel
  have hv : ((Generated.hostChunk082[8]).induced.toList, (Generated.hostChunk082[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 7, 0, 4, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 4, 0, 2, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0992]

theorem fixed_values_0993 :
    (fixedDensityCounts (maskGraph 7 380731), fixedComplementCounts (maskGraph 7 380731)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 1, 1, 2, 4, 2, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 2, 2, 2, 1, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0993_semantics :
    ((Generated.hostChunk082[9]).induced.toList, (Generated.hostChunk082[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[9]).mask)) := by
  have hm : (Generated.hostChunk082[9]).mask = 380731 := by decide +kernel
  have hv : ((Generated.hostChunk082[9]).induced.toList, (Generated.hostChunk082[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 1, 1, 2, 4, 2, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 2, 2, 2, 1, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0993]

theorem fixed_values_0994 :
    (fixedDensityCounts (maskGraph 7 380735), fixedComplementCounts (maskGraph 7 380735)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 2, 0, 9, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 5, 0, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0994_semantics :
    ((Generated.hostChunk082[10]).induced.toList, (Generated.hostChunk082[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[10]).mask)) := by
  have hm : (Generated.hostChunk082[10]).mask = 380735 := by decide +kernel
  have hv : ((Generated.hostChunk082[10]).induced.toList, (Generated.hostChunk082[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 2, 0, 9, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 5, 0, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0994]

theorem fixed_values_0995 :
    (fixedDensityCounts (maskGraph 7 380795), fixedComplementCounts (maskGraph 7 380795)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 0, 4, 0, 4, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 4, 0, 2, 4, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0995_semantics :
    ((Generated.hostChunk082[11]).induced.toList, (Generated.hostChunk082[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk082[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk082[11]).mask)) := by
  have hm : (Generated.hostChunk082[11]).mask = 380795 := by decide +kernel
  have hv : ((Generated.hostChunk082[11]).induced.toList, (Generated.hostChunk082[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 2, 0, 4, 0, 4, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 4, 0, 2, 4, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0995]

theorem fixed_chunk_082_semantics :
    ∀ h ∈ Generated.hostChunk082.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk082.toList = [Generated.hostChunk082[0], Generated.hostChunk082[1], Generated.hostChunk082[2], Generated.hostChunk082[3], Generated.hostChunk082[4], Generated.hostChunk082[5], Generated.hostChunk082[6], Generated.hostChunk082[7], Generated.hostChunk082[8], Generated.hostChunk082[9], Generated.hostChunk082[10], Generated.hostChunk082[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0984_semantics
  · exact fixed_host_0985_semantics
  · exact fixed_host_0986_semantics
  · exact fixed_host_0987_semantics
  · exact fixed_host_0988_semantics
  · exact fixed_host_0989_semantics
  · exact fixed_host_0990_semantics
  · exact fixed_host_0991_semantics
  · exact fixed_host_0992_semantics
  · exact fixed_host_0993_semantics
  · exact fixed_host_0994_semantics
  · exact fixed_host_0995_semantics

end InducedPentagons.Paper

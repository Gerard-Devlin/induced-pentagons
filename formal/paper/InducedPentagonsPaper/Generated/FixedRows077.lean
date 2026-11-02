import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData077
import InducedPentagonsPaper.Generated.FixedRows069

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0924 :
    (fixedDensityCounts (maskGraph 7 129023), fixedComplementCounts (maskGraph 7 129023)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 2, 6, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 2, 3, 0]) := by
  decide +kernel

theorem fixed_host_0924_semantics :
    ((Generated.hostChunk077[0]).induced.toList, (Generated.hostChunk077[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[0]).mask)) := by
  have hm : (Generated.hostChunk077[0]).mask = 129023 := by decide +kernel
  have hv : ((Generated.hostChunk077[0]).induced.toList, (Generated.hostChunk077[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 2, 6, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 2, 3, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0924]

theorem fixed_values_0925 :
    (fixedDensityCounts (maskGraph 7 131004), fixedComplementCounts (maskGraph 7 131004)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0]) := by
  decide +kernel

theorem fixed_host_0925_semantics :
    ((Generated.hostChunk077[1]).induced.toList, (Generated.hostChunk077[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[1]).mask)) := by
  have hm : (Generated.hostChunk077[1]).mask = 131004 := by decide +kernel
  have hv : ((Generated.hostChunk077[1]).induced.toList, (Generated.hostChunk077[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0925]

theorem fixed_values_0926 :
    (fixedDensityCounts (maskGraph 7 131005), fixedComplementCounts (maskGraph 7 131005)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 2, 1, 0]) := by
  decide +kernel

theorem fixed_host_0926_semantics :
    ((Generated.hostChunk077[2]).induced.toList, (Generated.hostChunk077[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[2]).mask)) := by
  have hm : (Generated.hostChunk077[2]).mask = 131005 := by decide +kernel
  have hv : ((Generated.hostChunk077[2]).induced.toList, (Generated.hostChunk077[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 2, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0926]

theorem fixed_values_0927 :
    (fixedDensityCounts (maskGraph 7 131007), fixedComplementCounts (maskGraph 7 131007)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 5, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3, 2, 0]) := by
  decide +kernel

theorem fixed_host_0927_semantics :
    ((Generated.hostChunk077[3]).induced.toList, (Generated.hostChunk077[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[3]).mask)) := by
  have hm : (Generated.hostChunk077[3]).mask = 131007 := by decide +kernel
  have hv : ((Generated.hostChunk077[3]).induced.toList, (Generated.hostChunk077[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 5, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0927]

theorem fixed_values_0928 :
    (fixedDensityCounts (maskGraph 7 131071), fixedComplementCounts (maskGraph 7 131071)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 7, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 0]) := by
  decide +kernel

theorem fixed_host_0928_semantics :
    ((Generated.hostChunk077[4]).induced.toList, (Generated.hostChunk077[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[4]).mask)) := by
  have hm : (Generated.hostChunk077[4]).mask = 131071 := by decide +kernel
  have hv : ((Generated.hostChunk077[4]).induced.toList, (Generated.hostChunk077[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 7, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0928]

theorem fixed_values_0929 :
    (fixedDensityCounts (maskGraph 7 259903), fixedComplementCounts (maskGraph 7 259903)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0]) := by
  decide +kernel

theorem fixed_host_0929_semantics :
    ((Generated.hostChunk077[5]).induced.toList, (Generated.hostChunk077[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[5]).mask)) := by
  have hm : (Generated.hostChunk077[5]).mask = 259903 := by decide +kernel
  have hv : ((Generated.hostChunk077[5]).induced.toList, (Generated.hostChunk077[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0929]

theorem fixed_values_0930 :
    (fixedDensityCounts (maskGraph 7 259963), fixedComplementCounts (maskGraph 7 259963)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 9, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 3, 0]) := by
  decide +kernel

theorem fixed_host_0930_semantics :
    ((Generated.hostChunk077[6]).induced.toList, (Generated.hostChunk077[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[6]).mask)) := by
  have hm : (Generated.hostChunk077[6]).mask = 259963 := by decide +kernel
  have hv : ((Generated.hostChunk077[6]).induced.toList, (Generated.hostChunk077[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 9, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 3, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0930]

theorem fixed_values_0931 :
    (fixedDensityCounts (maskGraph 7 259964), fixedComplementCounts (maskGraph 7 259964)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0931_semantics :
    ((Generated.hostChunk077[7]).induced.toList, (Generated.hostChunk077[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[7]).mask)) := by
  have hm : (Generated.hostChunk077[7]).mask = 259964 := by decide +kernel
  have hv : ((Generated.hostChunk077[7]).induced.toList, (Generated.hostChunk077[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 12, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0931]

theorem fixed_values_0932 :
    (fixedDensityCounts (maskGraph 7 259965), fixedComplementCounts (maskGraph 7 259965)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0]) := by
  decide +kernel

theorem fixed_host_0932_semantics :
    ((Generated.hostChunk077[8]).induced.toList, (Generated.hostChunk077[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[8]).mask)) := by
  have hm : (Generated.hostChunk077[8]).mask = 259965 := by decide +kernel
  have hv : ((Generated.hostChunk077[8]).induced.toList, (Generated.hostChunk077[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0932]

theorem fixed_values_0933 :
    (fixedDensityCounts (maskGraph 7 259967), fixedComplementCounts (maskGraph 7 259967)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 6, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 3, 0]) := by
  decide +kernel

theorem fixed_host_0933_semantics :
    ((Generated.hostChunk077[9]).induced.toList, (Generated.hostChunk077[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[9]).mask)) := by
  have hm : (Generated.hostChunk077[9]).mask = 259967 := by decide +kernel
  have hv : ((Generated.hostChunk077[9]).induced.toList, (Generated.hostChunk077[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 6, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 3, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0933]

theorem fixed_values_0934 :
    (fixedDensityCounts (maskGraph 7 260094), fixedComplementCounts (maskGraph 7 260094)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0]) := by
  decide +kernel

theorem fixed_host_0934_semantics :
    ((Generated.hostChunk077[10]).induced.toList, (Generated.hostChunk077[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[10]).mask)) := by
  have hm : (Generated.hostChunk077[10]).mask = 260094 := by decide +kernel
  have hv : ((Generated.hostChunk077[10]).induced.toList, (Generated.hostChunk077[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0934]

theorem fixed_values_0935 :
    (fixedDensityCounts (maskGraph 7 260095), fixedComplementCounts (maskGraph 7 260095)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 9, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0]) := by
  decide +kernel

theorem fixed_host_0935_semantics :
    ((Generated.hostChunk077[11]).induced.toList, (Generated.hostChunk077[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk077[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk077[11]).mask)) := by
  have hm : (Generated.hostChunk077[11]).mask = 260095 := by decide +kernel
  have hv : ((Generated.hostChunk077[11]).induced.toList, (Generated.hostChunk077[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 9, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0935]

theorem fixed_chunk_077_semantics :
    ∀ h ∈ Generated.hostChunk077.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk077.toList = [Generated.hostChunk077[0], Generated.hostChunk077[1], Generated.hostChunk077[2], Generated.hostChunk077[3], Generated.hostChunk077[4], Generated.hostChunk077[5], Generated.hostChunk077[6], Generated.hostChunk077[7], Generated.hostChunk077[8], Generated.hostChunk077[9], Generated.hostChunk077[10], Generated.hostChunk077[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0924_semantics
  · exact fixed_host_0925_semantics
  · exact fixed_host_0926_semantics
  · exact fixed_host_0927_semantics
  · exact fixed_host_0928_semantics
  · exact fixed_host_0929_semantics
  · exact fixed_host_0930_semantics
  · exact fixed_host_0931_semantics
  · exact fixed_host_0932_semantics
  · exact fixed_host_0933_semantics
  · exact fixed_host_0934_semantics
  · exact fixed_host_0935_semantics

end InducedPentagons.Paper

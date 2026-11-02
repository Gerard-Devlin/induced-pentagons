import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData080
import InducedPentagonsPaper.Generated.FixedRows072

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0960 :
    (fixedDensityCounts (maskGraph 7 376047), fixedComplementCounts (maskGraph 7 376047)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 7, 1, 0, 0, 0, 4, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 5, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0960_semantics :
    ((Generated.hostChunk080[0]).induced.toList, (Generated.hostChunk080[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[0]).mask)) := by
  have hm : (Generated.hostChunk080[0]).mask = 376047 := by decide +kernel
  have hv : ((Generated.hostChunk080[0]).induced.toList, (Generated.hostChunk080[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 7, 1, 0, 0, 0, 4, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 5, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0960]

theorem fixed_values_0961 :
    (fixedDensityCounts (maskGraph 7 376056), fixedComplementCounts (maskGraph 7 376056)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 8, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0961_semantics :
    ((Generated.hostChunk080[1]).induced.toList, (Generated.hostChunk080[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[1]).mask)) := by
  have hm : (Generated.hostChunk080[1]).mask = 376056 := by decide +kernel
  have hv : ((Generated.hostChunk080[1]).induced.toList, (Generated.hostChunk080[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 8, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0961]

theorem fixed_values_0962 :
    (fixedDensityCounts (maskGraph 7 376057), fixedComplementCounts (maskGraph 7 376057)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 2, 0, 4, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 2, 0, 4, 0, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0962_semantics :
    ((Generated.hostChunk080[2]).induced.toList, (Generated.hostChunk080[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[2]).mask)) := by
  have hm : (Generated.hostChunk080[2]).mask = 376057 := by decide +kernel
  have hv : ((Generated.hostChunk080[2]).induced.toList, (Generated.hostChunk080[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 2, 0, 4, 0, 4, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 2, 0, 4, 0, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0962]

theorem fixed_values_0963 :
    (fixedDensityCounts (maskGraph 7 376058), fixedComplementCounts (maskGraph 7 376058)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 6, 2, 0, 2, 3, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 2, 3, 0, 0, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0963_semantics :
    ((Generated.hostChunk080[3]).induced.toList, (Generated.hostChunk080[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[3]).mask)) := by
  have hm : (Generated.hostChunk080[3]).mask = 376058 := by decide +kernel
  have hv : ((Generated.hostChunk080[3]).induced.toList, (Generated.hostChunk080[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 6, 2, 0, 2, 3, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0, 2, 3, 0, 0, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0963]

theorem fixed_values_0964 :
    (fixedDensityCounts (maskGraph 7 376059), fixedComplementCounts (maskGraph 7 376059)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 5, 1, 1, 0, 2, 3, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 1, 1, 0, 2, 3, 0, 1, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0964_semantics :
    ((Generated.hostChunk080[4]).induced.toList, (Generated.hostChunk080[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[4]).mask)) := by
  have hm : (Generated.hostChunk080[4]).mask = 376059 := by decide +kernel
  have hv : ((Generated.hostChunk080[4]).induced.toList, (Generated.hostChunk080[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 5, 1, 1, 0, 2, 3, 1, 2, 2, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 1, 1, 0, 2, 3, 0, 1, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0964]

theorem fixed_values_0965 :
    (fixedDensityCounts (maskGraph 7 376062), fixedComplementCounts (maskGraph 7 376062)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 6, 0, 0, 4, 0, 1, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 0, 0, 4, 0, 1, 1, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0965_semantics :
    ((Generated.hostChunk080[5]).induced.toList, (Generated.hostChunk080[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[5]).mask)) := by
  have hm : (Generated.hostChunk080[5]).mask = 376062 := by decide +kernel
  have hv : ((Generated.hostChunk080[5]).induced.toList, (Generated.hostChunk080[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 6, 0, 0, 4, 0, 1, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 2, 0, 0, 4, 0, 1, 1, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0965]

theorem fixed_values_0966 :
    (fixedDensityCounts (maskGraph 7 376063), fixedComplementCounts (maskGraph 7 376063)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 4, 1, 0, 0, 4, 0, 4, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 1, 0, 0, 4, 0, 2, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0966_semantics :
    ((Generated.hostChunk080[6]).induced.toList, (Generated.hostChunk080[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[6]).mask)) := by
  have hm : (Generated.hostChunk080[6]).mask = 376063 := by decide +kernel
  have hv : ((Generated.hostChunk080[6]).induced.toList, (Generated.hostChunk080[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 4, 1, 0, 0, 4, 0, 4, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 1, 0, 0, 4, 0, 2, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0966]

theorem fixed_values_0967 :
    (fixedDensityCounts (maskGraph 7 376303), fixedComplementCounts (maskGraph 7 376303)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 9, 2, 0, 0, 0, 0, 0, 6, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 9, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0967_semantics :
    ((Generated.hostChunk080[7]).induced.toList, (Generated.hostChunk080[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[7]).mask)) := by
  have hm : (Generated.hostChunk080[7]).mask = 376303 := by decide +kernel
  have hv : ((Generated.hostChunk080[7]).induced.toList, (Generated.hostChunk080[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 9, 2, 0, 0, 0, 0, 0, 6, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 9, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0967]

theorem fixed_values_0968 :
    (fixedDensityCounts (maskGraph 7 376310), fixedComplementCounts (maskGraph 7 376310)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 2, 0, 1, 4, 2, 1, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 4, 0, 1, 0, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0968_semantics :
    ((Generated.hostChunk080[8]).induced.toList, (Generated.hostChunk080[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[8]).mask)) := by
  have hm : (Generated.hostChunk080[8]).mask = 376310 := by decide +kernel
  have hv : ((Generated.hostChunk080[8]).induced.toList, (Generated.hostChunk080[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 2, 0, 1, 4, 2, 1, 2, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 4, 0, 1, 0, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0968]

theorem fixed_values_0969 :
    (fixedDensityCounts (maskGraph 7 376311), fixedComplementCounts (maskGraph 7 376311)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 2, 0, 0, 1, 4, 0, 1, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 2, 0, 0, 1, 4, 0, 1, 0, 2, 0]) := by
  decide +kernel

theorem fixed_host_0969_semantics :
    ((Generated.hostChunk080[9]).induced.toList, (Generated.hostChunk080[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[9]).mask)) := by
  have hm : (Generated.hostChunk080[9]).mask = 376311 := by decide +kernel
  have hv : ((Generated.hostChunk080[9]).induced.toList, (Generated.hostChunk080[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 2, 0, 0, 1, 4, 0, 1, 2, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 2, 0, 0, 1, 4, 0, 1, 0, 2, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0969]

theorem fixed_values_0970 :
    (fixedDensityCounts (maskGraph 7 376318), fixedComplementCounts (maskGraph 7 376318)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 5, 0, 0, 3, 0, 3, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 3, 0, 3, 0, 0, 1, 1]) := by
  decide +kernel

theorem fixed_host_0970_semantics :
    ((Generated.hostChunk080[10]).induced.toList, (Generated.hostChunk080[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[10]).mask)) := by
  have hm : (Generated.hostChunk080[10]).mask = 376318 := by decide +kernel
  have hv : ((Generated.hostChunk080[10]).induced.toList, (Generated.hostChunk080[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 5, 0, 0, 3, 0, 3, 3, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 3, 0, 3, 0, 0, 1, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0970]

theorem fixed_values_0971 :
    (fixedDensityCounts (maskGraph 7 376319), fixedComplementCounts (maskGraph 7 376319)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 5, 0, 0, 0, 3, 0, 3, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 4, 0, 0, 0, 3, 0, 3, 0, 1, 1]) := by
  decide +kernel

theorem fixed_host_0971_semantics :
    ((Generated.hostChunk080[11]).induced.toList, (Generated.hostChunk080[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk080[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk080[11]).mask)) := by
  have hm : (Generated.hostChunk080[11]).mask = 376319 := by decide +kernel
  have hv : ((Generated.hostChunk080[11]).induced.toList, (Generated.hostChunk080[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 5, 0, 0, 0, 3, 0, 3, 0, 4, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 4, 0, 0, 0, 3, 0, 3, 0, 1, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0971]

theorem fixed_chunk_080_semantics :
    ∀ h ∈ Generated.hostChunk080.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk080.toList = [Generated.hostChunk080[0], Generated.hostChunk080[1], Generated.hostChunk080[2], Generated.hostChunk080[3], Generated.hostChunk080[4], Generated.hostChunk080[5], Generated.hostChunk080[6], Generated.hostChunk080[7], Generated.hostChunk080[8], Generated.hostChunk080[9], Generated.hostChunk080[10], Generated.hostChunk080[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0960_semantics
  · exact fixed_host_0961_semantics
  · exact fixed_host_0962_semantics
  · exact fixed_host_0963_semantics
  · exact fixed_host_0964_semantics
  · exact fixed_host_0965_semantics
  · exact fixed_host_0966_semantics
  · exact fixed_host_0967_semantics
  · exact fixed_host_0968_semantics
  · exact fixed_host_0969_semantics
  · exact fixed_host_0970_semantics
  · exact fixed_host_0971_semantics

end InducedPentagons.Paper

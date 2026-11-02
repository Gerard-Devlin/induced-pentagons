import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData017
import InducedPentagonsPaper.Generated.FixedRows009

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0204 :
    (fixedDensityCounts (maskGraph 7 6621), fixedComplementCounts (maskGraph 7 6621)) =
      ([0, 0, 2, 1, 0, 2, 0, 3, 2, 0, 0, 0, 1, 5, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 2, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0204_semantics :
    ((Generated.hostChunk017[0]).induced.toList, (Generated.hostChunk017[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[0]).mask)) := by
  have hm : (Generated.hostChunk017[0]).mask = 6621 := by decide +kernel
  have hv : ((Generated.hostChunk017[0]).induced.toList, (Generated.hostChunk017[0]).complement.toList) =
      ([0, 0, 2, 1, 0, 2, 0, 3, 2, 0, 0, 0, 1, 5, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 2, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0204]

theorem fixed_values_0205 :
    (fixedDensityCounts (maskGraph 7 6623), fixedComplementCounts (maskGraph 7 6623)) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 5, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 2, 1, 0, 2, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0205_semantics :
    ((Generated.hostChunk017[1]).induced.toList, (Generated.hostChunk017[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[1]).mask)) := by
  have hm : (Generated.hostChunk017[1]).mask = 6623 := by decide +kernel
  have hv : ((Generated.hostChunk017[1]).induced.toList, (Generated.hostChunk017[1]).complement.toList) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 5, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 2, 1, 0, 2, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0205]

theorem fixed_values_0206 :
    (fixedDensityCounts (maskGraph 7 6640), fixedComplementCounts (maskGraph 7 6640)) =
      ([0, 0, 3, 0, 0, 2, 0, 0, 0, 9, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0206_semantics :
    ((Generated.hostChunk017[2]).induced.toList, (Generated.hostChunk017[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[2]).mask)) := by
  have hm : (Generated.hostChunk017[2]).mask = 6640 := by decide +kernel
  have hv : ((Generated.hostChunk017[2]).induced.toList, (Generated.hostChunk017[2]).complement.toList) =
      ([0, 0, 3, 0, 0, 2, 0, 0, 0, 9, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0206]

theorem fixed_values_0207 :
    (fixedDensityCounts (maskGraph 7 6641), fixedComplementCounts (maskGraph 7 6641)) =
      ([0, 0, 3, 0, 0, 2, 0, 0, 0, 4, 5, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0207_semantics :
    ((Generated.hostChunk017[3]).induced.toList, (Generated.hostChunk017[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[3]).mask)) := by
  have hm : (Generated.hostChunk017[3]).mask = 6641 := by decide +kernel
  have hv : ((Generated.hostChunk017[3]).induced.toList, (Generated.hostChunk017[3]).complement.toList) =
      ([0, 0, 3, 0, 0, 2, 0, 0, 0, 4, 5, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0207]

theorem fixed_values_0208 :
    (fixedDensityCounts (maskGraph 7 6643), fixedComplementCounts (maskGraph 7 6643)) =
      ([0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 8, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0208_semantics :
    ((Generated.hostChunk017[4]).induced.toList, (Generated.hostChunk017[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[4]).mask)) := by
  have hm : (Generated.hostChunk017[4]).mask = 6643 := by decide +kernel
  have hv : ((Generated.hostChunk017[4]).induced.toList, (Generated.hostChunk017[4]).complement.toList) =
      ([0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 8, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0208]

theorem fixed_values_0209 :
    (fixedDensityCounts (maskGraph 7 6644), fixedComplementCounts (maskGraph 7 6644)) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 0, 3, 2, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0209_semantics :
    ((Generated.hostChunk017[5]).induced.toList, (Generated.hostChunk017[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[5]).mask)) := by
  have hm : (Generated.hostChunk017[5]).mask = 6644 := by decide +kernel
  have hv : ((Generated.hostChunk017[5]).induced.toList, (Generated.hostChunk017[5]).complement.toList) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 0, 3, 2, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0209]

theorem fixed_values_0210 :
    (fixedDensityCounts (maskGraph 7 6645), fixedComplementCounts (maskGraph 7 6645)) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 3, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0210_semantics :
    ((Generated.hostChunk017[6]).induced.toList, (Generated.hostChunk017[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[6]).mask)) := by
  have hm : (Generated.hostChunk017[6]).mask = 6645 := by decide +kernel
  have hv : ((Generated.hostChunk017[6]).induced.toList, (Generated.hostChunk017[6]).complement.toList) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 0, 1, 3, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0210]

theorem fixed_values_0211 :
    (fixedDensityCounts (maskGraph 7 6647), fixedComplementCounts (maskGraph 7 6647)) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 2, 3, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0211_semantics :
    ((Generated.hostChunk017[7]).induced.toList, (Generated.hostChunk017[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[7]).mask)) := by
  have hm : (Generated.hostChunk017[7]).mask = 6647 := by decide +kernel
  have hv : ((Generated.hostChunk017[7]).induced.toList, (Generated.hostChunk017[7]).complement.toList) =
      ([0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 2, 3, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0211]

theorem fixed_values_0212 :
    (fixedDensityCounts (maskGraph 7 6652), fixedComplementCounts (maskGraph 7 6652)) =
      ([0, 0, 2, 0, 1, 2, 0, 0, 0, 1, 4, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0212_semantics :
    ((Generated.hostChunk017[8]).induced.toList, (Generated.hostChunk017[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[8]).mask)) := by
  have hm : (Generated.hostChunk017[8]).mask = 6652 := by decide +kernel
  have hv : ((Generated.hostChunk017[8]).induced.toList, (Generated.hostChunk017[8]).complement.toList) =
      ([0, 0, 2, 0, 1, 2, 0, 0, 0, 1, 4, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0212]

theorem fixed_values_0213 :
    (fixedDensityCounts (maskGraph 7 6653), fixedComplementCounts (maskGraph 7 6653)) =
      ([0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 3, 2, 0, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0213_semantics :
    ((Generated.hostChunk017[9]).induced.toList, (Generated.hostChunk017[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[9]).mask)) := by
  have hm : (Generated.hostChunk017[9]).mask = 6653 := by decide +kernel
  have hv : ((Generated.hostChunk017[9]).induced.toList, (Generated.hostChunk017[9]).complement.toList) =
      ([0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 3, 2, 0, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0213]

theorem fixed_values_0214 :
    (fixedDensityCounts (maskGraph 7 6655), fixedComplementCounts (maskGraph 7 6655)) =
      ([0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0214_semantics :
    ((Generated.hostChunk017[10]).induced.toList, (Generated.hostChunk017[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[10]).mask)) := by
  have hm : (Generated.hostChunk017[10]).mask = 6655 := by decide +kernel
  have hv : ((Generated.hostChunk017[10]).induced.toList, (Generated.hostChunk017[10]).complement.toList) =
      ([0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0214]

theorem fixed_values_0215 :
    (fixedDensityCounts (maskGraph 7 6808), fixedComplementCounts (maskGraph 7 6808)) =
      ([0, 0, 6, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0215_semantics :
    ((Generated.hostChunk017[11]).induced.toList, (Generated.hostChunk017[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk017[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk017[11]).mask)) := by
  have hm : (Generated.hostChunk017[11]).mask = 6808 := by decide +kernel
  have hv : ((Generated.hostChunk017[11]).induced.toList, (Generated.hostChunk017[11]).complement.toList) =
      ([0, 0, 6, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0215]

theorem fixed_chunk_017_semantics :
    ∀ h ∈ Generated.hostChunk017.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk017.toList = [Generated.hostChunk017[0], Generated.hostChunk017[1], Generated.hostChunk017[2], Generated.hostChunk017[3], Generated.hostChunk017[4], Generated.hostChunk017[5], Generated.hostChunk017[6], Generated.hostChunk017[7], Generated.hostChunk017[8], Generated.hostChunk017[9], Generated.hostChunk017[10], Generated.hostChunk017[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0204_semantics
  · exact fixed_host_0205_semantics
  · exact fixed_host_0206_semantics
  · exact fixed_host_0207_semantics
  · exact fixed_host_0208_semantics
  · exact fixed_host_0209_semantics
  · exact fixed_host_0210_semantics
  · exact fixed_host_0211_semantics
  · exact fixed_host_0212_semantics
  · exact fixed_host_0213_semantics
  · exact fixed_host_0214_semantics
  · exact fixed_host_0215_semantics

end InducedPentagons.Paper

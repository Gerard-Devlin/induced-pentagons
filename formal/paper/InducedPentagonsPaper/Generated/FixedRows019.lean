import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData019
import InducedPentagonsPaper.Generated.FixedRows011

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0228 :
    (fixedDensityCounts (maskGraph 7 6828), fixedComplementCounts (maskGraph 7 6828)) =
      ([0, 0, 2, 1, 0, 0, 2, 5, 0, 2, 3, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0228_semantics :
    ((Generated.hostChunk019[0]).induced.toList, (Generated.hostChunk019[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[0]).mask)) := by
  have hm : (Generated.hostChunk019[0]).mask = 6828 := by decide +kernel
  have hv : ((Generated.hostChunk019[0]).induced.toList, (Generated.hostChunk019[0]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 2, 5, 0, 2, 3, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0228]

theorem fixed_values_0229 :
    (fixedDensityCounts (maskGraph 7 6829), fixedComplementCounts (maskGraph 7 6829)) =
      ([0, 0, 2, 1, 0, 0, 1, 5, 0, 0, 2, 1, 1, 0, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0229_semantics :
    ((Generated.hostChunk019[1]).induced.toList, (Generated.hostChunk019[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[1]).mask)) := by
  have hm : (Generated.hostChunk019[1]).mask = 6829 := by decide +kernel
  have hv : ((Generated.hostChunk019[1]).induced.toList, (Generated.hostChunk019[1]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 5, 0, 0, 2, 1, 1, 0, 2, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0229]

theorem fixed_values_0230 :
    (fixedDensityCounts (maskGraph 7 6830), fixedComplementCounts (maskGraph 7 6830)) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 3, 2, 1, 0, 0, 1, 3, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0230_semantics :
    ((Generated.hostChunk019[2]).induced.toList, (Generated.hostChunk019[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[2]).mask)) := by
  have hm : (Generated.hostChunk019[2]).mask = 6830 := by decide +kernel
  have hv : ((Generated.hostChunk019[2]).induced.toList, (Generated.hostChunk019[2]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 3, 2, 1, 0, 0, 1, 3, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0230]

theorem fixed_values_0231 :
    (fixedDensityCounts (maskGraph 7 6831), fixedComplementCounts (maskGraph 7 6831)) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 2, 0, 2, 2, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0231_semantics :
    ((Generated.hostChunk019[3]).induced.toList, (Generated.hostChunk019[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[3]).mask)) := by
  have hm : (Generated.hostChunk019[3]).mask = 6831 := by decide +kernel
  have hv : ((Generated.hostChunk019[3]).induced.toList, (Generated.hostChunk019[3]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 2, 0, 2, 2, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0231]

theorem fixed_values_0232 :
    (fixedDensityCounts (maskGraph 7 6840), fixedComplementCounts (maskGraph 7 6840)) =
      ([0, 0, 2, 1, 0, 0, 1, 4, 0, 3, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0232_semantics :
    ((Generated.hostChunk019[4]).induced.toList, (Generated.hostChunk019[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[4]).mask)) := by
  have hm : (Generated.hostChunk019[4]).mask = 6840 := by decide +kernel
  have hv : ((Generated.hostChunk019[4]).induced.toList, (Generated.hostChunk019[4]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 4, 0, 3, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0232]

theorem fixed_values_0233 :
    (fixedDensityCounts (maskGraph 7 6841), fixedComplementCounts (maskGraph 7 6841)) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 1, 1, 3, 1, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0233_semantics :
    ((Generated.hostChunk019[5]).induced.toList, (Generated.hostChunk019[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[5]).mask)) := by
  have hm : (Generated.hostChunk019[5]).mask = 6841 := by decide +kernel
  have hv : ((Generated.hostChunk019[5]).induced.toList, (Generated.hostChunk019[5]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 1, 1, 3, 1, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0233]

theorem fixed_values_0234 :
    (fixedDensityCounts (maskGraph 7 6843), fixedComplementCounts (maskGraph 7 6843)) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 0, 0, 2, 4, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0234_semantics :
    ((Generated.hostChunk019[6]).induced.toList, (Generated.hostChunk019[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[6]).mask)) := by
  have hm : (Generated.hostChunk019[6]).mask = 6843 := by decide +kernel
  have hv : ((Generated.hostChunk019[6]).induced.toList, (Generated.hostChunk019[6]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 1, 2, 0, 0, 2, 4, 0, 0, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0234]

theorem fixed_values_0235 :
    (fixedDensityCounts (maskGraph 7 6844), fixedComplementCounts (maskGraph 7 6844)) =
      ([0, 0, 2, 0, 1, 0, 1, 4, 0, 0, 5, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0235_semantics :
    ((Generated.hostChunk019[7]).induced.toList, (Generated.hostChunk019[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[7]).mask)) := by
  have hm : (Generated.hostChunk019[7]).mask = 6844 := by decide +kernel
  have hv : ((Generated.hostChunk019[7]).induced.toList, (Generated.hostChunk019[7]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 1, 4, 0, 0, 5, 0, 0, 0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0235]

theorem fixed_values_0236 :
    (fixedDensityCounts (maskGraph 7 6845), fixedComplementCounts (maskGraph 7 6845)) =
      ([0, 0, 2, 0, 1, 0, 1, 2, 1, 0, 3, 2, 0, 0, 1, 1, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0236_semantics :
    ((Generated.hostChunk019[8]).induced.toList, (Generated.hostChunk019[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[8]).mask)) := by
  have hm : (Generated.hostChunk019[8]).mask = 6845 := by decide +kernel
  have hv : ((Generated.hostChunk019[8]).induced.toList, (Generated.hostChunk019[8]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 1, 2, 1, 0, 3, 2, 0, 0, 1, 1, 2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0236]

theorem fixed_values_0237 :
    (fixedDensityCounts (maskGraph 7 6847), fixedComplementCounts (maskGraph 7 6847)) =
      ([0, 0, 2, 0, 1, 0, 1, 2, 0, 0, 0, 6, 0, 0, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0237_semantics :
    ((Generated.hostChunk019[9]).induced.toList, (Generated.hostChunk019[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[9]).mask)) := by
  have hm : (Generated.hostChunk019[9]).mask = 6847 := by decide +kernel
  have hv : ((Generated.hostChunk019[9]).induced.toList, (Generated.hostChunk019[9]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 1, 2, 0, 0, 0, 6, 0, 0, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0237]

theorem fixed_values_0238 :
    (fixedDensityCounts (maskGraph 7 6875), fixedComplementCounts (maskGraph 7 6875)) =
      ([0, 0, 3, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0238_semantics :
    ((Generated.hostChunk019[10]).induced.toList, (Generated.hostChunk019[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[10]).mask)) := by
  have hm : (Generated.hostChunk019[10]).mask = 6875 := by decide +kernel
  have hv : ((Generated.hostChunk019[10]).induced.toList, (Generated.hostChunk019[10]).complement.toList) =
      ([0, 0, 3, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0238]

theorem fixed_values_0239 :
    (fixedDensityCounts (maskGraph 7 6876), fixedComplementCounts (maskGraph 7 6876)) =
      ([0, 0, 2, 1, 0, 0, 0, 7, 3, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0239_semantics :
    ((Generated.hostChunk019[11]).induced.toList, (Generated.hostChunk019[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk019[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk019[11]).mask)) := by
  have hm : (Generated.hostChunk019[11]).mask = 6876 := by decide +kernel
  have hv : ((Generated.hostChunk019[11]).induced.toList, (Generated.hostChunk019[11]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 7, 3, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0239]

theorem fixed_chunk_019_semantics :
    ∀ h ∈ Generated.hostChunk019.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk019.toList = [Generated.hostChunk019[0], Generated.hostChunk019[1], Generated.hostChunk019[2], Generated.hostChunk019[3], Generated.hostChunk019[4], Generated.hostChunk019[5], Generated.hostChunk019[6], Generated.hostChunk019[7], Generated.hostChunk019[8], Generated.hostChunk019[9], Generated.hostChunk019[10], Generated.hostChunk019[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0228_semantics
  · exact fixed_host_0229_semantics
  · exact fixed_host_0230_semantics
  · exact fixed_host_0231_semantics
  · exact fixed_host_0232_semantics
  · exact fixed_host_0233_semantics
  · exact fixed_host_0234_semantics
  · exact fixed_host_0235_semantics
  · exact fixed_host_0236_semantics
  · exact fixed_host_0237_semantics
  · exact fixed_host_0238_semantics
  · exact fixed_host_0239_semantics

end InducedPentagons.Paper

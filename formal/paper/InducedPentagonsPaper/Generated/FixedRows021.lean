import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData021
import InducedPentagonsPaper.Generated.FixedRows013

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0252 :
    (fixedDensityCounts (maskGraph 7 6908), fixedComplementCounts (maskGraph 7 6908)) =
      ([0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 4, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0252_semantics :
    ((Generated.hostChunk021[0]).induced.toList, (Generated.hostChunk021[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[0]).mask)) := by
  have hm : (Generated.hostChunk021[0]).mask = 6908 := by decide +kernel
  have hv : ((Generated.hostChunk021[0]).induced.toList, (Generated.hostChunk021[0]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 4, 0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0252]

theorem fixed_values_0253 :
    (fixedDensityCounts (maskGraph 7 6909), fixedComplementCounts (maskGraph 7 6909)) =
      ([0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 2, 2, 0, 0, 0, 2, 3, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0253_semantics :
    ((Generated.hostChunk021[1]).induced.toList, (Generated.hostChunk021[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[1]).mask)) := by
  have hm : (Generated.hostChunk021[1]).mask = 6909 := by decide +kernel
  have hv : ((Generated.hostChunk021[1]).induced.toList, (Generated.hostChunk021[1]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 2, 2, 0, 0, 0, 2, 3, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0253]

theorem fixed_values_0254 :
    (fixedDensityCounts (maskGraph 7 6911), fixedComplementCounts (maskGraph 7 6911)) =
      ([0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 4, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0254_semantics :
    ((Generated.hostChunk021[2]).induced.toList, (Generated.hostChunk021[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[2]).mask)) := by
  have hm : (Generated.hostChunk021[2]).mask = 6911 := by decide +kernel
  have hv : ((Generated.hostChunk021[2]).induced.toList, (Generated.hostChunk021[2]).complement.toList) =
      ([0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 4, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0254]

theorem fixed_values_0255 :
    (fixedDensityCounts (maskGraph 7 7068), fixedComplementCounts (maskGraph 7 7068)) =
      ([0, 0, 2, 4, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0255_semantics :
    ((Generated.hostChunk021[3]).induced.toList, (Generated.hostChunk021[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[3]).mask)) := by
  have hm : (Generated.hostChunk021[3]).mask = 7068 := by decide +kernel
  have hv : ((Generated.hostChunk021[3]).induced.toList, (Generated.hostChunk021[3]).complement.toList) =
      ([0, 0, 2, 4, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0255]

theorem fixed_values_0256 :
    (fixedDensityCounts (maskGraph 7 7069), fixedComplementCounts (maskGraph 7 7069)) =
      ([0, 0, 1, 2, 0, 1, 0, 4, 2, 0, 0, 0, 2, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0256_semantics :
    ((Generated.hostChunk021[4]).induced.toList, (Generated.hostChunk021[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[4]).mask)) := by
  have hm : (Generated.hostChunk021[4]).mask = 7069 := by decide +kernel
  have hv : ((Generated.hostChunk021[4]).induced.toList, (Generated.hostChunk021[4]).complement.toList) =
      ([0, 0, 1, 2, 0, 1, 0, 4, 2, 0, 0, 0, 2, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0256]

theorem fixed_values_0257 :
    (fixedDensityCounts (maskGraph 7 7070), fixedComplementCounts (maskGraph 7 7070)) =
      ([0, 0, 1, 2, 0, 0, 0, 3, 4, 0, 0, 0, 4, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0257_semantics :
    ((Generated.hostChunk021[5]).induced.toList, (Generated.hostChunk021[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[5]).mask)) := by
  have hm : (Generated.hostChunk021[5]).mask = 7070 := by decide +kernel
  have hv : ((Generated.hostChunk021[5]).induced.toList, (Generated.hostChunk021[5]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 3, 4, 0, 0, 0, 4, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0257]

theorem fixed_values_0258 :
    (fixedDensityCounts (maskGraph 7 7071), fixedComplementCounts (maskGraph 7 7071)) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 3, 0, 0, 0, 1, 6, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0258_semantics :
    ((Generated.hostChunk021[6]).induced.toList, (Generated.hostChunk021[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[6]).mask)) := by
  have hm : (Generated.hostChunk021[6]).mask = 7071 := by decide +kernel
  have hv : ((Generated.hostChunk021[6]).induced.toList, (Generated.hostChunk021[6]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 3, 0, 0, 0, 1, 6, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0258]

theorem fixed_values_0259 :
    (fixedDensityCounts (maskGraph 7 7084), fixedComplementCounts (maskGraph 7 7084)) =
      ([0, 0, 1, 2, 0, 0, 1, 4, 0, 0, 4, 0, 2, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0259_semantics :
    ((Generated.hostChunk021[7]).induced.toList, (Generated.hostChunk021[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[7]).mask)) := by
  have hm : (Generated.hostChunk021[7]).mask = 7084 := by decide +kernel
  have hv : ((Generated.hostChunk021[7]).induced.toList, (Generated.hostChunk021[7]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 1, 4, 0, 0, 4, 0, 2, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0259]

theorem fixed_values_0260 :
    (fixedDensityCounts (maskGraph 7 7085), fixedComplementCounts (maskGraph 7 7085)) =
      ([0, 0, 1, 2, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 6, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0260_semantics :
    ((Generated.hostChunk021[8]).induced.toList, (Generated.hostChunk021[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[8]).mask)) := by
  have hm : (Generated.hostChunk021[8]).mask = 7085 := by decide +kernel
  have hv : ((Generated.hostChunk021[8]).induced.toList, (Generated.hostChunk021[8]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 6, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0260]

theorem fixed_values_0261 :
    (fixedDensityCounts (maskGraph 7 7086), fixedComplementCounts (maskGraph 7 7086)) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 2, 1, 0, 0, 1, 1, 2, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0261_semantics :
    ((Generated.hostChunk021[9]).induced.toList, (Generated.hostChunk021[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[9]).mask)) := by
  have hm : (Generated.hostChunk021[9]).mask = 7086 := by decide +kernel
  have hv : ((Generated.hostChunk021[9]).induced.toList, (Generated.hostChunk021[9]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 2, 1, 0, 0, 1, 1, 2, 2, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0261]

theorem fixed_values_0262 :
    (fixedDensityCounts (maskGraph 7 7087), fixedComplementCounts (maskGraph 7 7087)) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 2, 0, 1, 0, 1, 1, 0, 2, 1, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0262_semantics :
    ((Generated.hostChunk021[10]).induced.toList, (Generated.hostChunk021[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[10]).mask)) := by
  have hm : (Generated.hostChunk021[10]).mask = 7087 := by decide +kernel
  have hv : ((Generated.hostChunk021[10]).induced.toList, (Generated.hostChunk021[10]).complement.toList) =
      ([0, 0, 1, 2, 0, 0, 0, 2, 2, 0, 1, 0, 1, 1, 0, 2, 1, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0262]

theorem fixed_values_0263 :
    (fixedDensityCounts (maskGraph 7 7088), fixedComplementCounts (maskGraph 7 7088)) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 0, 7, 1, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0263_semantics :
    ((Generated.hostChunk021[11]).induced.toList, (Generated.hostChunk021[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk021[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk021[11]).mask)) := by
  have hm : (Generated.hostChunk021[11]).mask = 7088 := by decide +kernel
  have hv : ((Generated.hostChunk021[11]).induced.toList, (Generated.hostChunk021[11]).complement.toList) =
      ([0, 0, 2, 1, 0, 0, 0, 3, 0, 7, 1, 0, 2, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0263]

theorem fixed_chunk_021_semantics :
    ∀ h ∈ Generated.hostChunk021.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk021.toList = [Generated.hostChunk021[0], Generated.hostChunk021[1], Generated.hostChunk021[2], Generated.hostChunk021[3], Generated.hostChunk021[4], Generated.hostChunk021[5], Generated.hostChunk021[6], Generated.hostChunk021[7], Generated.hostChunk021[8], Generated.hostChunk021[9], Generated.hostChunk021[10], Generated.hostChunk021[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0252_semantics
  · exact fixed_host_0253_semantics
  · exact fixed_host_0254_semantics
  · exact fixed_host_0255_semantics
  · exact fixed_host_0256_semantics
  · exact fixed_host_0257_semantics
  · exact fixed_host_0258_semantics
  · exact fixed_host_0259_semantics
  · exact fixed_host_0260_semantics
  · exact fixed_host_0261_semantics
  · exact fixed_host_0262_semantics
  · exact fixed_host_0263_semantics

end InducedPentagons.Paper

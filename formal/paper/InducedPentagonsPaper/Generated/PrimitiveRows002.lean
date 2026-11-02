import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData002

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0024 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 206) = [10, 0, 0, 0, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0024_semantics :
    (Generated.hostChunk002[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[0]).mask = 206 := by decide +kernel
  have hv : (Generated.hostChunk002[0]).primitive.toList = [10, 0, 0, 0, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0024]
  rfl

theorem primitive_values_0025 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 207) = [12, 0, 0, 0, 0, 22, 30, 20, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0025_semantics :
    (Generated.hostChunk002[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[1]).mask = 207 := by decide +kernel
  have hv : (Generated.hostChunk002[1]).primitive.toList = [12, 0, 0, 0, 0, 22, 30, 20, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0025]
  rfl

theorem primitive_values_0026 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 216) = [8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0026_semantics :
    (Generated.hostChunk002[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[2]).mask = 216 := by decide +kernel
  have hv : (Generated.hostChunk002[2]).primitive.toList = [8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0026]
  rfl

theorem primitive_values_0027 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 217) = [10, 0, 0, 0, 0, 12, 12, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0027_semantics :
    (Generated.hostChunk002[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[3]).mask = 217 := by decide +kernel
  have hv : (Generated.hostChunk002[3]).primitive.toList = [10, 0, 0, 0, 0, 12, 12, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0027]
  rfl

theorem primitive_values_0028 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 218) = [10, 0, 0, 0, 0, 10, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0028_semantics :
    (Generated.hostChunk002[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[4]).mask = 218 := by decide +kernel
  have hv : (Generated.hostChunk002[4]).primitive.toList = [10, 0, 0, 0, 0, 10, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0028]
  rfl

theorem primitive_values_0029 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 219) = [12, 0, 0, 0, 0, 20, 30, 16, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0029_semantics :
    (Generated.hostChunk002[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[5]).mask = 219 := by decide +kernel
  have hv : (Generated.hostChunk002[5]).primitive.toList = [12, 0, 0, 0, 0, 20, 30, 16, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0029]
  rfl

theorem primitive_values_0030 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 222) = [12, 0, 0, 0, 0, 18, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0030_semantics :
    (Generated.hostChunk002[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[6]).mask = 222 := by decide +kernel
  have hv : (Generated.hostChunk002[6]).primitive.toList = [12, 0, 0, 0, 0, 18, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0030]
  rfl

theorem primitive_values_0031 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 223) = [14, 0, 0, 0, 0, 30, 66, 28, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0031_semantics :
    (Generated.hostChunk002[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[7]).mask = 223 := by decide +kernel
  have hv : (Generated.hostChunk002[7]).primitive.toList = [14, 0, 0, 0, 0, 30, 66, 28, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0031]
  rfl

theorem primitive_values_0032 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 248) = [10, 0, 0, 0, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0032_semantics :
    (Generated.hostChunk002[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[8]).mask = 248 := by decide +kernel
  have hv : (Generated.hostChunk002[8]).primitive.toList = [10, 0, 0, 0, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0032]
  rfl

theorem primitive_values_0033 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 249) = [12, 0, 0, 0, 0, 18, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0033_semantics :
    (Generated.hostChunk002[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[9]).mask = 249 := by decide +kernel
  have hv : (Generated.hostChunk002[9]).primitive.toList = [12, 0, 0, 0, 0, 18, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0033]
  rfl

theorem primitive_values_0034 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 250) = [12, 0, 0, 0, 0, 16, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0034_semantics :
    (Generated.hostChunk002[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[10]).mask = 250 := by decide +kernel
  have hv : (Generated.hostChunk002[10]).primitive.toList = [12, 0, 0, 0, 0, 16, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0034]
  rfl

theorem primitive_values_0035 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 251) = [14, 0, 0, 0, 0, 28, 66, 22, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0035_semantics :
    (Generated.hostChunk002[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk002[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk002[11]).mask = 251 := by decide +kernel
  have hv : (Generated.hostChunk002[11]).primitive.toList = [14, 0, 0, 0, 0, 28, 66, 22, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0035]
  rfl

theorem primitive_chunk_002_semantics :
    ∀ h ∈ Generated.hostChunk002.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk002.toList = [Generated.hostChunk002[0], Generated.hostChunk002[1], Generated.hostChunk002[2], Generated.hostChunk002[3], Generated.hostChunk002[4], Generated.hostChunk002[5], Generated.hostChunk002[6], Generated.hostChunk002[7], Generated.hostChunk002[8], Generated.hostChunk002[9], Generated.hostChunk002[10], Generated.hostChunk002[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0024_semantics
  · exact primitive_host_0025_semantics
  · exact primitive_host_0026_semantics
  · exact primitive_host_0027_semantics
  · exact primitive_host_0028_semantics
  · exact primitive_host_0029_semantics
  · exact primitive_host_0030_semantics
  · exact primitive_host_0031_semantics
  · exact primitive_host_0032_semantics
  · exact primitive_host_0033_semantics
  · exact primitive_host_0034_semantics
  · exact primitive_host_0035_semantics

end InducedPentagons.Paper

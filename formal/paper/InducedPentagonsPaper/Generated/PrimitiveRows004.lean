import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData004

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0048 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 510) = [16, 0, 0, 0, 0, 32, 66, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0048_semantics :
    (Generated.hostChunk004[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[0]).mask = 510 := by decide +kernel
  have hv : (Generated.hostChunk004[0]).primitive.toList = [16, 0, 0, 0, 0, 32, 66, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0048]
  rfl

theorem primitive_values_0049 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 511) = [18, 0, 0, 0, 0, 48, 144, 60, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0049_semantics :
    (Generated.hostChunk004[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[1]).mask = 511 := by decide +kernel
  have hv : (Generated.hostChunk004[1]).primitive.toList = [18, 0, 0, 0, 0, 48, 144, 60, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0049]
  rfl

theorem primitive_values_0050 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 990) = [16, 0, 0, 0, 0, 32, 48, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0050_semantics :
    (Generated.hostChunk004[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[2]).mask = 990 := by decide +kernel
  have hv : (Generated.hostChunk004[2]).primitive.toList = [16, 0, 0, 0, 0, 32, 48, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0050]
  rfl

theorem primitive_values_0051 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 991) = [18, 0, 0, 0, 0, 48, 120, 72, 0, 48, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0051_semantics :
    (Generated.hostChunk004[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[3]).mask = 991 := by decide +kernel
  have hv : (Generated.hostChunk004[3]).primitive.toList = [18, 0, 0, 0, 0, 48, 120, 72, 0, 48, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0051]
  rfl

theorem primitive_values_0052 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1006) = [16, 0, 0, 0, 0, 30, 48, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0052_semantics :
    (Generated.hostChunk004[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[4]).mask = 1006 := by decide +kernel
  have hv : (Generated.hostChunk004[4]).primitive.toList = [16, 0, 0, 0, 0, 30, 48, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0052]
  rfl

theorem primitive_values_0053 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1007) = [18, 0, 0, 0, 0, 46, 120, 62, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0053_semantics :
    (Generated.hostChunk004[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[5]).mask = 1007 := by decide +kernel
  have hv : (Generated.hostChunk004[5]).primitive.toList = [18, 0, 0, 0, 0, 46, 120, 62, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0053]
  rfl

theorem primitive_values_0054 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1022) = [18, 0, 0, 0, 0, 40, 84, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0054_semantics :
    (Generated.hostChunk004[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[6]).mask = 1022 := by decide +kernel
  have hv : (Generated.hostChunk004[6]).primitive.toList = [18, 0, 0, 0, 0, 40, 84, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0054]
  rfl

theorem primitive_values_0055 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1023) = [20, 0, 0, 0, 0, 58, 180, 88, 0, 56, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0055_semantics :
    (Generated.hostChunk004[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[7]).mask = 1023 := by decide +kernel
  have hv : (Generated.hostChunk004[7]).primitive.toList = [20, 0, 0, 0, 0, 58, 180, 88, 0, 56, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0055]
  rfl

theorem primitive_values_0056 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2046) = [20, 0, 0, 0, 0, 50, 120, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0056_semantics :
    (Generated.hostChunk004[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[8]).mask = 2046 := by decide +kernel
  have hv : (Generated.hostChunk004[8]).primitive.toList = [20, 0, 0, 0, 0, 50, 120, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0056]
  rfl

theorem primitive_values_0057 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2047) = [22, 0, 0, 0, 0, 70, 240, 120, 0, 80, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0057_semantics :
    (Generated.hostChunk004[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[9]).mask = 2047 := by decide +kernel
  have hv : (Generated.hostChunk004[9]).primitive.toList = [22, 0, 0, 0, 0, 70, 240, 120, 0, 80, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0057]
  rfl

theorem primitive_values_0058 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2247) = [12, 0, 0, 0, 0, 24, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0058_semantics :
    (Generated.hostChunk004[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[10]).mask = 2247 := by decide +kernel
  have hv : (Generated.hostChunk004[10]).primitive.toList = [12, 0, 0, 0, 0, 24, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0058]
  rfl

theorem primitive_values_0059 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2248) = [8, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0059_semantics :
    (Generated.hostChunk004[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk004[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk004[11]).mask = 2248 := by decide +kernel
  have hv : (Generated.hostChunk004[11]).primitive.toList = [8, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0059]
  rfl

theorem primitive_chunk_004_semantics :
    ∀ h ∈ Generated.hostChunk004.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk004.toList = [Generated.hostChunk004[0], Generated.hostChunk004[1], Generated.hostChunk004[2], Generated.hostChunk004[3], Generated.hostChunk004[4], Generated.hostChunk004[5], Generated.hostChunk004[6], Generated.hostChunk004[7], Generated.hostChunk004[8], Generated.hostChunk004[9], Generated.hostChunk004[10], Generated.hostChunk004[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0048_semantics
  · exact primitive_host_0049_semantics
  · exact primitive_host_0050_semantics
  · exact primitive_host_0051_semantics
  · exact primitive_host_0052_semantics
  · exact primitive_host_0053_semantics
  · exact primitive_host_0054_semantics
  · exact primitive_host_0055_semantics
  · exact primitive_host_0056_semantics
  · exact primitive_host_0057_semantics
  · exact primitive_host_0058_semantics
  · exact primitive_host_0059_semantics

end InducedPentagons.Paper

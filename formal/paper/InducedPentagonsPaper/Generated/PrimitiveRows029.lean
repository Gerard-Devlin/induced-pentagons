import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData029
import InducedPentagonsPaper.Generated.PrimitiveRows021

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0348 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15871) = [26, 0, 0, 0, 0, 86, 252, 198, 0, 140, 36, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84] := by
  decide +kernel

theorem primitive_host_0348_semantics :
    (Generated.hostChunk029[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[0]).mask = 15871 := by decide +kernel
  have hv : (Generated.hostChunk029[0]).primitive.toList = [26, 0, 0, 0, 0, 86, 252, 198, 0, 140, 36, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84] := by decide +kernel
  rw [hm, hv, primitive_values_0348]
  rfl

theorem primitive_values_0349 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 16316) = [22, 0, 0, 0, 0, 50, 72, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0349_semantics :
    (Generated.hostChunk029[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[1]).mask = 16316 := by decide +kernel
  have hv : (Generated.hostChunk029[1]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0349]
  rfl

theorem primitive_values_0350 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 16317) = [24, 0, 0, 0, 0, 66, 144, 144, 0, 54, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0350_semantics :
    (Generated.hostChunk029[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[2]).mask = 16317 := by decide +kernel
  have hv : (Generated.hostChunk029[2]).primitive.toList = [24, 0, 0, 0, 0, 66, 144, 144, 0, 54, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0350]
  rfl

theorem primitive_values_0351 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 16318) = [24, 0, 0, 0, 0, 64, 126, 140, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0351_semantics :
    (Generated.hostChunk029[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[3]).mask = 16318 := by decide +kernel
  have hv : (Generated.hostChunk029[3]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 140, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0351]
  rfl

theorem primitive_values_0352 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 16319) = [26, 0, 0, 0, 0, 82, 222, 190, 0, 104, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0352_semantics :
    (Generated.hostChunk029[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[4]).mask = 16319 := by decide +kernel
  have hv : (Generated.hostChunk029[4]).primitive.toList = [26, 0, 0, 0, 0, 82, 222, 190, 0, 104, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0352]
  rfl

theorem primitive_values_0353 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 16382) = [26, 0, 0, 0, 0, 80, 198, 188, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0353_semantics :
    (Generated.hostChunk029[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[5]).mask = 16382 := by decide +kernel
  have hv : (Generated.hostChunk029[5]).primitive.toList = [26, 0, 0, 0, 0, 80, 198, 188, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0353]
  rfl

theorem primitive_values_0354 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 16383) = [28, 0, 0, 0, 0, 100, 318, 252, 0, 188, 52, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 124] := by
  decide +kernel

theorem primitive_host_0354_semantics :
    (Generated.hostChunk029[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[6]).mask = 16383 := by decide +kernel
  have hv : (Generated.hostChunk029[6]).primitive.toList = [28, 0, 0, 0, 0, 100, 318, 252, 0, 188, 52, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 124] := by decide +kernel
  rw [hm, hv, primitive_values_0354]
  rfl

theorem primitive_values_0355 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 32700) = [24, 0, 0, 0, 0, 60, 96, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0355_semantics :
    (Generated.hostChunk029[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[7]).mask = 32700 := by decide +kernel
  have hv : (Generated.hostChunk029[7]).primitive.toList = [24, 0, 0, 0, 0, 60, 96, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0355]
  rfl

theorem primitive_values_0356 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 32701) = [26, 0, 0, 0, 0, 76, 168, 184, 0, 56, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0356_semantics :
    (Generated.hostChunk029[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[8]).mask = 32701 := by decide +kernel
  have hv : (Generated.hostChunk029[8]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 184, 0, 56, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0356]
  rfl

theorem primitive_values_0357 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 32703) = [28, 0, 0, 0, 0, 94, 264, 240, 0, 128, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0357_semantics :
    (Generated.hostChunk029[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[9]).mask = 32703 := by decide +kernel
  have hv : (Generated.hostChunk029[9]).primitive.toList = [28, 0, 0, 0, 0, 94, 264, 240, 0, 128, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0357]
  rfl

theorem primitive_values_0358 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 32767) = [30, 0, 0, 0, 0, 114, 384, 312, 0, 240, 72, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0358_semantics :
    (Generated.hostChunk029[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[10]).mask = 32767 := by decide +kernel
  have hv : (Generated.hostChunk029[10]).primitive.toList = [30, 0, 0, 0, 0, 114, 384, 312, 0, 240, 72, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0358]
  rfl

theorem primitive_values_0359 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39375) = [20, 0, 0, 0, 0, 60, 120, 120, 0, 120, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0359_semantics :
    (Generated.hostChunk029[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk029[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk029[11]).mask = 39375 := by decide +kernel
  have hv : (Generated.hostChunk029[11]).primitive.toList = [20, 0, 0, 0, 0, 60, 120, 120, 0, 120, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0359]
  rfl

theorem primitive_chunk_029_semantics :
    ∀ h ∈ Generated.hostChunk029.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk029.toList = [Generated.hostChunk029[0], Generated.hostChunk029[1], Generated.hostChunk029[2], Generated.hostChunk029[3], Generated.hostChunk029[4], Generated.hostChunk029[5], Generated.hostChunk029[6], Generated.hostChunk029[7], Generated.hostChunk029[8], Generated.hostChunk029[9], Generated.hostChunk029[10], Generated.hostChunk029[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0348_semantics
  · exact primitive_host_0349_semantics
  · exact primitive_host_0350_semantics
  · exact primitive_host_0351_semantics
  · exact primitive_host_0352_semantics
  · exact primitive_host_0353_semantics
  · exact primitive_host_0354_semantics
  · exact primitive_host_0355_semantics
  · exact primitive_host_0356_semantics
  · exact primitive_host_0357_semantics
  · exact primitive_host_0358_semantics
  · exact primitive_host_0359_semantics

end InducedPentagons.Paper

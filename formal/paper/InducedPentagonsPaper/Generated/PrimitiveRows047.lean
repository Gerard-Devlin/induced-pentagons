import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData047
import InducedPentagonsPaper.Generated.PrimitiveRows039

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0564 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44013) = [22, 0, 0, 0, 0, 58, 120, 110, 0, 68, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0564_semantics :
    (Generated.hostChunk047[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[0]).mask = 44013 := by decide +kernel
  have hv : (Generated.hostChunk047[0]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 110, 0, 68, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0564]
  rfl

theorem primitive_values_0565 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44014) = [22, 0, 0, 0, 0, 56, 102, 108, 0, 52, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0565_semantics :
    (Generated.hostChunk047[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[1]).mask = 44014 := by decide +kernel
  have hv : (Generated.hostChunk047[1]).primitive.toList = [22, 0, 0, 0, 0, 56, 102, 108, 0, 52, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0565]
  rfl

theorem primitive_values_0566 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44015) = [24, 0, 0, 0, 0, 72, 174, 156, 0, 108, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0566_semantics :
    (Generated.hostChunk047[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[2]).mask = 44015 := by decide +kernel
  have hv : (Generated.hostChunk047[2]).primitive.toList = [24, 0, 0, 0, 0, 72, 174, 156, 0, 108, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0566]
  rfl

theorem primitive_values_0567 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44024) = [20, 10, 10, 0, 0, 42, 54, 70, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0567_semantics :
    (Generated.hostChunk047[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[3]).mask = 44024 := by decide +kernel
  have hv : (Generated.hostChunk047[3]).primitive.toList = [20, 10, 10, 0, 0, 42, 54, 70, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0567]
  rfl

theorem primitive_values_0568 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44025) = [22, 10, 12, 4, 0, 56, 108, 106, 0, 54, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0568_semantics :
    (Generated.hostChunk047[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[4]).mask = 44025 := by decide +kernel
  have hv : (Generated.hostChunk047[4]).primitive.toList = [22, 10, 12, 4, 0, 56, 108, 106, 0, 54, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0568]
  rfl

theorem primitive_values_0569 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44026) = [22, 0, 0, 0, 0, 54, 90, 104, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0569_semantics :
    (Generated.hostChunk047[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[5]).mask = 44026 := by decide +kernel
  have hv : (Generated.hostChunk047[5]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 104, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0569]
  rfl

theorem primitive_values_0570 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44027) = [24, 0, 0, 0, 0, 70, 162, 150, 0, 90, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0570_semantics :
    (Generated.hostChunk047[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[6]).mask = 44027 := by decide +kernel
  have hv : (Generated.hostChunk047[6]).primitive.toList = [24, 0, 0, 0, 0, 70, 162, 150, 0, 90, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0570]
  rfl

theorem primitive_values_0571 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44030) = [24, 0, 0, 0, 0, 68, 144, 146, 0, 70, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0571_semantics :
    (Generated.hostChunk047[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[7]).mask = 44030 := by decide +kernel
  have hv : (Generated.hostChunk047[7]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 146, 0, 70, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0571]
  rfl

theorem primitive_values_0572 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44031) = [26, 0, 0, 0, 0, 86, 240, 202, 0, 150, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0572_semantics :
    (Generated.hostChunk047[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[8]).mask = 44031 := by decide +kernel
  have hv : (Generated.hostChunk047[8]).primitive.toList = [26, 0, 0, 0, 0, 86, 240, 202, 0, 150, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0572]
  rfl

theorem primitive_values_0573 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44280) = [18, 30, 18, 0, 18, 30, 24, 42, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0573_semantics :
    (Generated.hostChunk047[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[9]).mask = 44280 := by decide +kernel
  have hv : (Generated.hostChunk047[9]).primitive.toList = [18, 30, 18, 0, 18, 30, 24, 42, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0573]
  rfl

theorem primitive_values_0574 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44281) = [20, 10, 8, 4, 8, 42, 60, 70, 4, 16, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0574_semantics :
    (Generated.hostChunk047[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[10]).mask = 44281 := by decide +kernel
  have hv : (Generated.hostChunk047[10]).primitive.toList = [20, 10, 8, 4, 8, 42, 60, 70, 4, 16, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0574]
  rfl

theorem primitive_values_0575 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44283) = [22, 0, 0, 0, 0, 56, 114, 106, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 12] := by
  decide +kernel

theorem primitive_host_0575_semantics :
    (Generated.hostChunk047[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk047[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk047[11]).mask = 44283 := by decide +kernel
  have hv : (Generated.hostChunk047[11]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 106, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0575]
  rfl

theorem primitive_chunk_047_semantics :
    ∀ h ∈ Generated.hostChunk047.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk047.toList = [Generated.hostChunk047[0], Generated.hostChunk047[1], Generated.hostChunk047[2], Generated.hostChunk047[3], Generated.hostChunk047[4], Generated.hostChunk047[5], Generated.hostChunk047[6], Generated.hostChunk047[7], Generated.hostChunk047[8], Generated.hostChunk047[9], Generated.hostChunk047[10], Generated.hostChunk047[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0564_semantics
  · exact primitive_host_0565_semantics
  · exact primitive_host_0566_semantics
  · exact primitive_host_0567_semantics
  · exact primitive_host_0568_semantics
  · exact primitive_host_0569_semantics
  · exact primitive_host_0570_semantics
  · exact primitive_host_0571_semantics
  · exact primitive_host_0572_semantics
  · exact primitive_host_0573_semantics
  · exact primitive_host_0574_semantics
  · exact primitive_host_0575_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData049
import InducedPentagonsPaper.Generated.PrimitiveRows041

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0588 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44404) = [18, 30, 20, 0, 12, 30, 24, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0588_semantics :
    (Generated.hostChunk049[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[0]).mask = 44404 := by decide +kernel
  have hv : (Generated.hostChunk049[0]).primitive.toList = [18, 30, 20, 0, 12, 30, 24, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0588]
  rfl

theorem primitive_values_0589 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44405) = [20, 0, 0, 0, 0, 42, 60, 76, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0589_semantics :
    (Generated.hostChunk049[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[1]).mask = 44405 := by decide +kernel
  have hv : (Generated.hostChunk049[1]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 76, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0589]
  rfl

theorem primitive_values_0590 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44406) = [20, 10, 8, 4, 8, 42, 60, 72, 4, 18, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0590_semantics :
    (Generated.hostChunk049[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[2]).mask = 44406 := by decide +kernel
  have hv : (Generated.hostChunk049[2]).primitive.toList = [20, 10, 8, 4, 8, 42, 60, 72, 4, 18, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0590]
  rfl

theorem primitive_values_0591 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44407) = [22, 0, 0, 0, 0, 56, 114, 108, 0, 46, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0591_semantics :
    (Generated.hostChunk049[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[3]).mask = 44407 := by decide +kernel
  have hv : (Generated.hostChunk049[3]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 108, 0, 46, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0591]
  rfl

theorem primitive_values_0592 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44412) = [20, 30, 28, 12, 8, 40, 48, 70, 4, 8, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0592_semantics :
    (Generated.hostChunk049[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[4]).mask = 44412 := by decide +kernel
  have hv : (Generated.hostChunk049[4]).primitive.toList = [20, 30, 28, 12, 8, 40, 48, 70, 4, 8, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0592]
  rfl

theorem primitive_values_0593 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44413) = [22, 0, 0, 0, 0, 54, 102, 104, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 8] := by
  decide +kernel

theorem primitive_host_0593_semantics :
    (Generated.hostChunk049[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[5]).mask = 44413 := by decide +kernel
  have hv : (Generated.hostChunk049[5]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 104, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0593]
  rfl

theorem primitive_values_0594 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44415) = [24, 0, 0, 0, 0, 70, 180, 146, 0, 80, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0594_semantics :
    (Generated.hostChunk049[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[6]).mask = 44415 := by decide +kernel
  have hv : (Generated.hostChunk049[6]).primitive.toList = [24, 0, 0, 0, 0, 70, 180, 146, 0, 80, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0594]
  rfl

theorem primitive_values_0595 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44460) = [18, 0, 0, 0, 0, 34, 42, 54, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0595_semantics :
    (Generated.hostChunk049[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[7]).mask = 44460 := by decide +kernel
  have hv : (Generated.hostChunk049[7]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 54, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0595]
  rfl

theorem primitive_values_0596 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44461) = [20, 0, 0, 0, 0, 46, 78, 78, 0, 50, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0596_semantics :
    (Generated.hostChunk049[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[8]).mask = 44461 := by decide +kernel
  have hv : (Generated.hostChunk049[8]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 78, 0, 50, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0596]
  rfl

theorem primitive_values_0597 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44462) = [20, 0, 0, 0, 0, 44, 66, 78, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0597_semantics :
    (Generated.hostChunk049[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[9]).mask = 44462 := by decide +kernel
  have hv : (Generated.hostChunk049[9]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 78, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0597]
  rfl

theorem primitive_values_0598 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44463) = [22, 0, 0, 0, 0, 58, 120, 112, 0, 70, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0598_semantics :
    (Generated.hostChunk049[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[10]).mask = 44463 := by decide +kernel
  have hv : (Generated.hostChunk049[10]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 112, 0, 70, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0598]
  rfl

theorem primitive_values_0599 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44466) = [18, 10, 8, 0, 0, 30, 24, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0599_semantics :
    (Generated.hostChunk049[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk049[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk049[11]).mask = 44466 := by decide +kernel
  have hv : (Generated.hostChunk049[11]).primitive.toList = [18, 10, 8, 0, 0, 30, 24, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0599]
  rfl

theorem primitive_chunk_049_semantics :
    ∀ h ∈ Generated.hostChunk049.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk049.toList = [Generated.hostChunk049[0], Generated.hostChunk049[1], Generated.hostChunk049[2], Generated.hostChunk049[3], Generated.hostChunk049[4], Generated.hostChunk049[5], Generated.hostChunk049[6], Generated.hostChunk049[7], Generated.hostChunk049[8], Generated.hostChunk049[9], Generated.hostChunk049[10], Generated.hostChunk049[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0588_semantics
  · exact primitive_host_0589_semantics
  · exact primitive_host_0590_semantics
  · exact primitive_host_0591_semantics
  · exact primitive_host_0592_semantics
  · exact primitive_host_0593_semantics
  · exact primitive_host_0594_semantics
  · exact primitive_host_0595_semantics
  · exact primitive_host_0596_semantics
  · exact primitive_host_0597_semantics
  · exact primitive_host_0598_semantics
  · exact primitive_host_0599_semantics

end InducedPentagons.Paper

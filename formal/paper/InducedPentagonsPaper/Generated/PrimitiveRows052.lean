import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData052
import InducedPentagonsPaper.Generated.PrimitiveRows044

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0624 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44857) = [20, 20, 16, 8, 16, 42, 60, 70, 8, 28, 12, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0624_semantics :
    (Generated.hostChunk052[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[0]).mask = 44857 := by decide +kernel
  have hv : (Generated.hostChunk052[0]).primitive.toList = [20, 20, 16, 8, 16, 42, 60, 70, 8, 28, 12, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0624]
  rfl

theorem primitive_values_0625 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44858) = [20, 10, 8, 0, 8, 40, 48, 72, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0625_semantics :
    (Generated.hostChunk052[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[1]).mask = 44858 := by decide +kernel
  have hv : (Generated.hostChunk052[1]).primitive.toList = [20, 10, 8, 0, 8, 40, 48, 72, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0625]
  rfl

theorem primitive_values_0626 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44859) = [22, 10, 10, 4, 10, 54, 102, 102, 4, 44, 16, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0626_semantics :
    (Generated.hostChunk052[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[2]).mask = 44859 := by decide +kernel
  have hv : (Generated.hostChunk052[2]).primitive.toList = [22, 10, 10, 4, 10, 54, 102, 102, 4, 44, 16, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0626]
  rfl

theorem primitive_values_0627 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44862) = [22, 10, 10, 0, 10, 52, 90, 98, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0627_semantics :
    (Generated.hostChunk052[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[3]).mask = 44862 := by decide +kernel
  have hv : (Generated.hostChunk052[3]).primitive.toList = [22, 10, 10, 0, 10, 52, 90, 98, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0627]
  rfl

theorem primitive_values_0628 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44863) = [24, 10, 12, 4, 12, 68, 168, 138, 4, 76, 28, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0628_semantics :
    (Generated.hostChunk052[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[4]).mask = 44863 := by decide +kernel
  have hv : (Generated.hostChunk052[4]).primitive.toList = [24, 10, 12, 4, 12, 68, 168, 138, 4, 76, 28, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0628]
  rfl

theorem primitive_values_0629 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44922) = [22, 0, 0, 0, 0, 52, 84, 106, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0629_semantics :
    (Generated.hostChunk052[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[5]).mask = 44922 := by decide +kernel
  have hv : (Generated.hostChunk052[5]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 106, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0629]
  rfl

theorem primitive_values_0630 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44923) = [24, 0, 0, 0, 0, 68, 156, 146, 0, 80, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0630_semantics :
    (Generated.hostChunk052[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[6]).mask = 44923 := by decide +kernel
  have hv : (Generated.hostChunk052[6]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 146, 0, 80, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0630]
  rfl

theorem primitive_values_0631 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44924) = [22, 10, 12, 8, 0, 50, 72, 96, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0631_semantics :
    (Generated.hostChunk052[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[7]).mask = 44924 := by decide +kernel
  have hv : (Generated.hostChunk052[7]).primitive.toList = [22, 10, 12, 8, 0, 50, 72, 96, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0631]
  rfl

theorem primitive_values_0632 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44925) = [24, 0, 0, 0, 0, 66, 144, 138, 0, 60, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0632_semantics :
    (Generated.hostChunk052[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[8]).mask = 44925 := by decide +kernel
  have hv : (Generated.hostChunk052[8]).primitive.toList = [24, 0, 0, 0, 0, 66, 144, 138, 0, 60, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0632]
  rfl

theorem primitive_values_0633 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44926) = [24, 0, 0, 0, 0, 64, 126, 136, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0633_semantics :
    (Generated.hostChunk052[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[9]).mask = 44926 := by decide +kernel
  have hv : (Generated.hostChunk052[9]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 136, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0633]
  rfl

theorem primitive_values_0634 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44927) = [26, 0, 0, 0, 0, 82, 222, 188, 0, 116, 36, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0634_semantics :
    (Generated.hostChunk052[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[10]).mask = 44927 := by decide +kernel
  have hv : (Generated.hostChunk052[10]).primitive.toList = [26, 0, 0, 0, 0, 82, 222, 188, 0, 116, 36, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0634]
  rfl

theorem primitive_values_0635 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 45054) = [26, 0, 0, 0, 0, 78, 180, 182, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0635_semantics :
    (Generated.hostChunk052[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk052[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk052[11]).mask = 45054 := by decide +kernel
  have hv : (Generated.hostChunk052[11]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 182, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0635]
  rfl

theorem primitive_chunk_052_semantics :
    ∀ h ∈ Generated.hostChunk052.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk052.toList = [Generated.hostChunk052[0], Generated.hostChunk052[1], Generated.hostChunk052[2], Generated.hostChunk052[3], Generated.hostChunk052[4], Generated.hostChunk052[5], Generated.hostChunk052[6], Generated.hostChunk052[7], Generated.hostChunk052[8], Generated.hostChunk052[9], Generated.hostChunk052[10], Generated.hostChunk052[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0624_semantics
  · exact primitive_host_0625_semantics
  · exact primitive_host_0626_semantics
  · exact primitive_host_0627_semantics
  · exact primitive_host_0628_semantics
  · exact primitive_host_0629_semantics
  · exact primitive_host_0630_semantics
  · exact primitive_host_0631_semantics
  · exact primitive_host_0632_semantics
  · exact primitive_host_0633_semantics
  · exact primitive_host_0634_semantics
  · exact primitive_host_0635_semantics

end InducedPentagons.Paper

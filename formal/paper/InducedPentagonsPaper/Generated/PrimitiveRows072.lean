import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData072
import InducedPentagonsPaper.Generated.PrimitiveRows064

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0864 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114175) = [30, 0, 0, 0, 0, 110, 330, 304, 0, 240, 36, 0, 0, 144, 0, 0, 0, 0, 0, 0, 4, 180] := by
  decide +kernel

theorem primitive_host_0864_semantics :
    (Generated.hostChunk072[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[0]).mask = 114175 := by decide +kernel
  have hv : (Generated.hostChunk072[0]).primitive.toList = [30, 0, 0, 0, 0, 110, 330, 304, 0, 240, 36, 0, 0, 144, 0, 0, 0, 0, 0, 0, 4, 180] := by decide +kernel
  rw [hm, hv, primitive_values_0864]
  rfl

theorem primitive_values_0865 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114489) = [24, 0, 0, 0, 0, 62, 108, 128, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0865_semantics :
    (Generated.hostChunk072[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[1]).mask = 114489 := by decide +kernel
  have hv : (Generated.hostChunk072[1]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 128, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0865]
  rfl

theorem primitive_values_0866 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114490) = [24, 0, 0, 0, 0, 62, 108, 136, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0866_semantics :
    (Generated.hostChunk072[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[2]).mask = 114490 := by decide +kernel
  have hv : (Generated.hostChunk072[2]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 136, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0866]
  rfl

theorem primitive_values_0867 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114491) = [26, 0, 0, 0, 0, 76, 162, 176, 0, 86, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0867_semantics :
    (Generated.hostChunk072[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[3]).mask = 114491 := by decide +kernel
  have hv : (Generated.hostChunk072[3]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 176, 0, 86, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0867]
  rfl

theorem primitive_values_0868 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114494) = [26, 0, 0, 0, 0, 76, 162, 180, 0, 94, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0868_semantics :
    (Generated.hostChunk072[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[4]).mask = 114494 := by decide +kernel
  have hv : (Generated.hostChunk072[4]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 180, 0, 94, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0868]
  rfl

theorem primitive_values_0869 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114495) = [28, 0, 0, 0, 0, 92, 240, 232, 0, 148, 40, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 88] := by
  decide +kernel

theorem primitive_host_0869_semantics :
    (Generated.hostChunk072[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[5]).mask = 114495 := by decide +kernel
  have hv : (Generated.hostChunk072[5]).primitive.toList = [28, 0, 0, 0, 0, 92, 240, 232, 0, 148, 40, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 88] := by decide +kernel
  rw [hm, hv, primitive_values_0869]
  rfl

theorem primitive_values_0870 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114554) = [26, 0, 0, 0, 0, 76, 162, 184, 0, 80, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0870_semantics :
    (Generated.hostChunk072[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[6]).mask = 114554 := by decide +kernel
  have hv : (Generated.hostChunk072[6]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 184, 0, 80, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0870]
  rfl

theorem primitive_values_0871 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114555) = [28, 0, 0, 0, 0, 92, 234, 236, 0, 150, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by
  decide +kernel

theorem primitive_host_0871_semantics :
    (Generated.hostChunk072[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[7]).mask = 114555 := by decide +kernel
  have hv : (Generated.hostChunk072[7]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 236, 0, 150, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by decide +kernel
  rw [hm, hv, primitive_values_0871]
  rfl

theorem primitive_values_0872 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114556) = [26, 10, 16, 16, 0, 74, 144, 174, 0, 72, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0872_semantics :
    (Generated.hostChunk072[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[8]).mask = 114556 := by decide +kernel
  have hv : (Generated.hostChunk072[8]).primitive.toList = [26, 10, 16, 16, 0, 74, 144, 174, 0, 72, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0872]
  rfl

theorem primitive_values_0873 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114557) = [28, 0, 0, 0, 0, 90, 216, 228, 0, 124, 56, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 56] := by
  decide +kernel

theorem primitive_host_0873_semantics :
    (Generated.hostChunk072[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[9]).mask = 114557 := by decide +kernel
  have hv : (Generated.hostChunk072[9]).primitive.toList = [28, 0, 0, 0, 0, 90, 216, 228, 0, 124, 56, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0873]
  rfl

theorem primitive_values_0874 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114558) = [28, 0, 0, 0, 0, 90, 216, 232, 0, 132, 32, 0, 4, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0874_semantics :
    (Generated.hostChunk072[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[10]).mask = 114558 := by decide +kernel
  have hv : (Generated.hostChunk072[10]).primitive.toList = [28, 0, 0, 0, 0, 90, 216, 232, 0, 132, 32, 0, 4, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0874]
  rfl

theorem primitive_values_0875 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114559) = [30, 0, 0, 0, 0, 108, 312, 298, 0, 216, 52, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 148] := by
  decide +kernel

theorem primitive_host_0875_semantics :
    (Generated.hostChunk072[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk072[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk072[11]).mask = 114559 := by decide +kernel
  have hv : (Generated.hostChunk072[11]).primitive.toList = [30, 0, 0, 0, 0, 108, 312, 298, 0, 216, 52, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 148] := by decide +kernel
  rw [hm, hv, primitive_values_0875]
  rfl

theorem primitive_chunk_072_semantics :
    ∀ h ∈ Generated.hostChunk072.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk072.toList = [Generated.hostChunk072[0], Generated.hostChunk072[1], Generated.hostChunk072[2], Generated.hostChunk072[3], Generated.hostChunk072[4], Generated.hostChunk072[5], Generated.hostChunk072[6], Generated.hostChunk072[7], Generated.hostChunk072[8], Generated.hostChunk072[9], Generated.hostChunk072[10], Generated.hostChunk072[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0864_semantics
  · exact primitive_host_0865_semantics
  · exact primitive_host_0866_semantics
  · exact primitive_host_0867_semantics
  · exact primitive_host_0868_semantics
  · exact primitive_host_0869_semantics
  · exact primitive_host_0870_semantics
  · exact primitive_host_0871_semantics
  · exact primitive_host_0872_semantics
  · exact primitive_host_0873_semantics
  · exact primitive_host_0874_semantics
  · exact primitive_host_0875_semantics

end InducedPentagons.Paper

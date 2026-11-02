import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData058
import InducedPentagonsPaper.Generated.PrimitiveRows050

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0696 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48757) = [22, 0, 0, 0, 0, 52, 84, 94, 0, 34, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0696_semantics :
    (Generated.hostChunk058[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[0]).mask = 48757 := by decide +kernel
  have hv : (Generated.hostChunk058[0]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 94, 0, 34, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0696]
  rfl

theorem primitive_values_0697 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48758) = [22, 0, 0, 0, 0, 54, 102, 102, 0, 42, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0697_semantics :
    (Generated.hostChunk058[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[1]).mask = 48758 := by decide +kernel
  have hv : (Generated.hostChunk058[1]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 102, 0, 42, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0697]
  rfl

theorem primitive_values_0698 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48759) = [24, 0, 0, 0, 0, 68, 156, 140, 0, 86, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0698_semantics :
    (Generated.hostChunk058[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[2]).mask = 48759 := by decide +kernel
  have hv : (Generated.hostChunk058[2]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 140, 0, 86, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0698]
  rfl

theorem primitive_values_0699 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48764) = [22, 20, 24, 16, 0, 50, 72, 92, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0699_semantics :
    (Generated.hostChunk058[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[3]).mask = 48764 := by decide +kernel
  have hv : (Generated.hostChunk058[3]).primitive.toList = [22, 20, 24, 16, 0, 50, 72, 92, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0699]
  rfl

theorem primitive_values_0700 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48765) = [24, 0, 0, 0, 0, 64, 126, 130, 0, 50, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0700_semantics :
    (Generated.hostChunk058[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[4]).mask = 48765 := by decide +kernel
  have hv : (Generated.hostChunk058[4]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 130, 0, 50, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0700]
  rfl

theorem primitive_values_0701 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48766) = [24, 0, 0, 0, 0, 66, 144, 136, 0, 72, 12, 0, 8, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0701_semantics :
    (Generated.hostChunk058[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[5]).mask = 48766 := by decide +kernel
  have hv : (Generated.hostChunk058[5]).primitive.toList = [24, 0, 0, 0, 0, 66, 144, 136, 0, 72, 12, 0, 8, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0701]
  rfl

theorem primitive_values_0702 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48767) = [26, 0, 0, 0, 0, 82, 222, 184, 0, 126, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0702_semantics :
    (Generated.hostChunk058[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[6]).mask = 48767 := by decide +kernel
  have hv : (Generated.hostChunk058[6]).primitive.toList = [26, 0, 0, 0, 0, 82, 222, 184, 0, 126, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0702]
  rfl

theorem primitive_values_0703 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48820) = [20, 0, 0, 0, 0, 40, 48, 72, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0703_semantics :
    (Generated.hostChunk058[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[7]).mask = 48820 := by decide +kernel
  have hv : (Generated.hostChunk058[7]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 72, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0703]
  rfl

theorem primitive_values_0704 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48821) = [22, 0, 0, 0, 0, 52, 84, 96, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0704_semantics :
    (Generated.hostChunk058[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[8]).mask = 48821 := by decide +kernel
  have hv : (Generated.hostChunk058[8]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 96, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0704]
  rfl

theorem primitive_values_0705 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48822) = [22, 0, 0, 0, 0, 52, 84, 102, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0705_semantics :
    (Generated.hostChunk058[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[9]).mask = 48822 := by decide +kernel
  have hv : (Generated.hostChunk058[9]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 102, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0705]
  rfl

theorem primitive_values_0706 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48823) = [24, 0, 0, 0, 0, 66, 138, 138, 0, 70, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0706_semantics :
    (Generated.hostChunk058[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[10]).mask = 48823 := by decide +kernel
  have hv : (Generated.hostChunk058[10]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 138, 0, 70, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0706]
  rfl

theorem primitive_values_0707 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48824) = [20, 20, 18, 0, 8, 38, 36, 66, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0707_semantics :
    (Generated.hostChunk058[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk058[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk058[11]).mask = 48824 := by decide +kernel
  have hv : (Generated.hostChunk058[11]).primitive.toList = [20, 20, 18, 0, 8, 38, 36, 66, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0707]
  rfl

theorem primitive_chunk_058_semantics :
    ∀ h ∈ Generated.hostChunk058.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk058.toList = [Generated.hostChunk058[0], Generated.hostChunk058[1], Generated.hostChunk058[2], Generated.hostChunk058[3], Generated.hostChunk058[4], Generated.hostChunk058[5], Generated.hostChunk058[6], Generated.hostChunk058[7], Generated.hostChunk058[8], Generated.hostChunk058[9], Generated.hostChunk058[10], Generated.hostChunk058[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0696_semantics
  · exact primitive_host_0697_semantics
  · exact primitive_host_0698_semantics
  · exact primitive_host_0699_semantics
  · exact primitive_host_0700_semantics
  · exact primitive_host_0701_semantics
  · exact primitive_host_0702_semantics
  · exact primitive_host_0703_semantics
  · exact primitive_host_0704_semantics
  · exact primitive_host_0705_semantics
  · exact primitive_host_0706_semantics
  · exact primitive_host_0707_semantics

end InducedPentagons.Paper

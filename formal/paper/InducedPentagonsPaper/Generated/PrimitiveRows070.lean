import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData070
import InducedPentagonsPaper.Generated.PrimitiveRows062

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0840 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114029) = [24, 0, 0, 0, 0, 64, 120, 132, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0840_semantics :
    (Generated.hostChunk070[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[0]).mask = 114029 := by decide +kernel
  have hv : (Generated.hostChunk070[0]).primitive.toList = [24, 0, 0, 0, 0, 64, 120, 132, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0840]
  rfl

theorem primitive_values_0841 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114031) = [26, 0, 0, 0, 0, 80, 192, 186, 0, 124, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by
  decide +kernel

theorem primitive_host_0841_semantics :
    (Generated.hostChunk070[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[1]).mask = 114031 := by decide +kernel
  have hv : (Generated.hostChunk070[1]).primitive.toList = [26, 0, 0, 0, 0, 80, 192, 186, 0, 124, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by decide +kernel
  rw [hm, hv, primitive_values_0841]
  rfl

theorem primitive_values_0842 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114034) = [22, 0, 0, 0, 0, 52, 90, 96, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0842_semantics :
    (Generated.hostChunk070[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[2]).mask = 114034 := by decide +kernel
  have hv : (Generated.hostChunk070[2]).primitive.toList = [22, 0, 0, 0, 0, 52, 90, 96, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0842]
  rfl

theorem primitive_values_0843 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114035) = [24, 10, 14, 8, 0, 64, 126, 130, 0, 66, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0843_semantics :
    (Generated.hostChunk070[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[3]).mask = 114035 := by decide +kernel
  have hv : (Generated.hostChunk070[3]).primitive.toList = [24, 10, 14, 8, 0, 64, 126, 130, 0, 66, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0843]
  rfl

theorem primitive_values_0844 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114036) = [22, 30, 32, 16, 20, 50, 72, 90, 8, 36, 12, 4, 0, 0, 0, 0, 8, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0844_semantics :
    (Generated.hostChunk070[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[4]).mask = 114036 := by decide +kernel
  have hv : (Generated.hostChunk070[4]).primitive.toList = [22, 30, 32, 16, 20, 50, 72, 90, 8, 36, 12, 4, 0, 0, 0, 0, 8, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0844]
  rfl

theorem primitive_values_0845 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114037) = [24, 0, 0, 0, 0, 62, 108, 126, 0, 48, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0845_semantics :
    (Generated.hostChunk070[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[5]).mask = 114037 := by decide +kernel
  have hv : (Generated.hostChunk070[5]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 126, 0, 48, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0845]
  rfl

theorem primitive_values_0846 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114038) = [24, 10, 12, 8, 12, 64, 126, 132, 8, 70, 12, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0846_semantics :
    (Generated.hostChunk070[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[6]).mask = 114038 := by decide +kernel
  have hv : (Generated.hostChunk070[6]).primitive.toList = [24, 10, 12, 8, 12, 64, 126, 132, 8, 70, 12, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0846]
  rfl

theorem primitive_values_0847 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114039) = [26, 0, 0, 0, 0, 78, 180, 178, 0, 104, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0847_semantics :
    (Generated.hostChunk070[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[7]).mask = 114039 := by decide +kernel
  have hv : (Generated.hostChunk070[7]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 178, 0, 104, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0847]
  rfl

theorem primitive_values_0848 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114040) = [22, 10, 10, 4, 10, 50, 72, 96, 4, 28, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0848_semantics :
    (Generated.hostChunk070[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[8]).mask = 114040 := by decide +kernel
  have hv : (Generated.hostChunk070[8]).primitive.toList = [22, 10, 10, 4, 10, 50, 72, 96, 4, 28, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0848]
  rfl

theorem primitive_values_0849 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114041) = [24, 0, 0, 0, 0, 62, 108, 128, 0, 50, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0849_semantics :
    (Generated.hostChunk070[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[9]).mask = 114041 := by decide +kernel
  have hv : (Generated.hostChunk070[9]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 128, 0, 50, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0849]
  rfl

theorem primitive_values_0850 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114042) = [24, 0, 0, 0, 0, 64, 126, 138, 0, 60, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0850_semantics :
    (Generated.hostChunk070[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[10]).mask = 114042 := by decide +kernel
  have hv : (Generated.hostChunk070[10]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 138, 0, 60, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0850]
  rfl

theorem primitive_values_0851 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114043) = [26, 0, 0, 0, 0, 78, 180, 180, 0, 106, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by
  decide +kernel

theorem primitive_host_0851_semantics :
    (Generated.hostChunk070[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk070[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk070[11]).mask = 114043 := by decide +kernel
  have hv : (Generated.hostChunk070[11]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 180, 0, 106, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0851]
  rfl

theorem primitive_chunk_070_semantics :
    ∀ h ∈ Generated.hostChunk070.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk070.toList = [Generated.hostChunk070[0], Generated.hostChunk070[1], Generated.hostChunk070[2], Generated.hostChunk070[3], Generated.hostChunk070[4], Generated.hostChunk070[5], Generated.hostChunk070[6], Generated.hostChunk070[7], Generated.hostChunk070[8], Generated.hostChunk070[9], Generated.hostChunk070[10], Generated.hostChunk070[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0840_semantics
  · exact primitive_host_0841_semantics
  · exact primitive_host_0842_semantics
  · exact primitive_host_0843_semantics
  · exact primitive_host_0844_semantics
  · exact primitive_host_0845_semantics
  · exact primitive_host_0846_semantics
  · exact primitive_host_0847_semantics
  · exact primitive_host_0848_semantics
  · exact primitive_host_0849_semantics
  · exact primitive_host_0850_semantics
  · exact primitive_host_0851_semantics

end InducedPentagons.Paper

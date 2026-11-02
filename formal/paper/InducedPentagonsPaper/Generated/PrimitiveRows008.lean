import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData008
import InducedPentagonsPaper.Generated.PrimitiveRows000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0096 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2417) = [12, 0, 0, 0, 0, 14, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0096_semantics :
    (Generated.hostChunk008[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[0]).mask = 2417 := by decide +kernel
  have hv : (Generated.hostChunk008[0]).primitive.toList = [12, 0, 0, 0, 0, 14, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0096]
  rfl

theorem primitive_values_0097 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2419) = [14, 0, 0, 0, 0, 24, 36, 26, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0097_semantics :
    (Generated.hostChunk008[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[1]).mask = 2419 := by decide +kernel
  have hv : (Generated.hostChunk008[1]).primitive.toList = [14, 0, 0, 0, 0, 24, 36, 26, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0097]
  rfl

theorem primitive_values_0098 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2420) = [12, 0, 0, 0, 0, 12, 6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0098_semantics :
    (Generated.hostChunk008[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[2]).mask = 2420 := by decide +kernel
  have hv : (Generated.hostChunk008[2]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0098]
  rfl

theorem primitive_values_0099 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2421) = [14, 0, 0, 0, 0, 22, 30, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0099_semantics :
    (Generated.hostChunk008[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[3]).mask = 2421 := by decide +kernel
  have hv : (Generated.hostChunk008[3]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0099]
  rfl

theorem primitive_values_0100 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2422) = [14, 0, 0, 0, 0, 22, 30, 20, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0100_semantics :
    (Generated.hostChunk008[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[4]).mask = 2422 := by decide +kernel
  have hv : (Generated.hostChunk008[4]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 20, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0100]
  rfl

theorem primitive_values_0101 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2423) = [16, 0, 0, 0, 0, 34, 72, 40, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0101_semantics :
    (Generated.hostChunk008[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[5]).mask = 2423 := by decide +kernel
  have hv : (Generated.hostChunk008[5]).primitive.toList = [16, 0, 0, 0, 0, 34, 72, 40, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0101]
  rfl

theorem primitive_values_0102 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2428) = [14, 10, 4, 4, 0, 20, 24, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0102_semantics :
    (Generated.hostChunk008[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[6]).mask = 2428 := by decide +kernel
  have hv : (Generated.hostChunk008[6]).primitive.toList = [14, 10, 4, 4, 0, 20, 24, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0102]
  rfl

theorem primitive_values_0103 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2429) = [16, 0, 0, 0, 0, 32, 66, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0103_semantics :
    (Generated.hostChunk008[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[7]).mask = 2429 := by decide +kernel
  have hv : (Generated.hostChunk008[7]).primitive.toList = [16, 0, 0, 0, 0, 32, 66, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0103]
  rfl

theorem primitive_values_0104 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2431) = [18, 0, 0, 0, 0, 46, 132, 58, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0104_semantics :
    (Generated.hostChunk008[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[8]).mask = 2431 := by decide +kernel
  have hv : (Generated.hostChunk008[8]).primitive.toList = [18, 0, 0, 0, 0, 46, 132, 58, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0104]
  rfl

theorem primitive_values_0105 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2510) = [14, 0, 0, 0, 0, 26, 24, 36, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0105_semantics :
    (Generated.hostChunk008[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[9]).mask = 2510 := by decide +kernel
  have hv : (Generated.hostChunk008[9]).primitive.toList = [14, 0, 0, 0, 0, 26, 24, 36, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0105]
  rfl

theorem primitive_values_0106 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2511) = [16, 0, 0, 0, 0, 38, 60, 56, 0, 44, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0106_semantics :
    (Generated.hostChunk008[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[10]).mask = 2511 := by decide +kernel
  have hv : (Generated.hostChunk008[10]).primitive.toList = [16, 0, 0, 0, 0, 38, 60, 56, 0, 44, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0106]
  rfl

theorem primitive_values_0107 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2518) = [14, 0, 0, 0, 0, 24, 24, 28, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0107_semantics :
    (Generated.hostChunk008[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk008[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk008[11]).mask = 2518 := by decide +kernel
  have hv : (Generated.hostChunk008[11]).primitive.toList = [14, 0, 0, 0, 0, 24, 24, 28, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0107]
  rfl

theorem primitive_chunk_008_semantics :
    ∀ h ∈ Generated.hostChunk008.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk008.toList = [Generated.hostChunk008[0], Generated.hostChunk008[1], Generated.hostChunk008[2], Generated.hostChunk008[3], Generated.hostChunk008[4], Generated.hostChunk008[5], Generated.hostChunk008[6], Generated.hostChunk008[7], Generated.hostChunk008[8], Generated.hostChunk008[9], Generated.hostChunk008[10], Generated.hostChunk008[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0096_semantics
  · exact primitive_host_0097_semantics
  · exact primitive_host_0098_semantics
  · exact primitive_host_0099_semantics
  · exact primitive_host_0100_semantics
  · exact primitive_host_0101_semantics
  · exact primitive_host_0102_semantics
  · exact primitive_host_0103_semantics
  · exact primitive_host_0104_semantics
  · exact primitive_host_0105_semantics
  · exact primitive_host_0106_semantics
  · exact primitive_host_0107_semantics

end InducedPentagons.Paper

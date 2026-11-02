import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData044
import InducedPentagonsPaper.Generated.PrimitiveRows036

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0528 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42495) = [24, 0, 0, 0, 0, 72, 198, 146, 0, 94, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0528_semantics :
    (Generated.hostChunk044[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[0]).mask = 42495 := by decide +kernel
  have hv : (Generated.hostChunk044[0]).primitive.toList = [24, 0, 0, 0, 0, 72, 198, 146, 0, 94, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0528]
  rfl

theorem primitive_values_0529 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43006) = [24, 0, 0, 0, 0, 66, 144, 136, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0529_semantics :
    (Generated.hostChunk044[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[1]).mask = 43006 := by decide +kernel
  have hv : (Generated.hostChunk044[1]).primitive.toList = [24, 0, 0, 0, 0, 66, 144, 136, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0529]
  rfl

theorem primitive_values_0530 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43007) = [26, 0, 0, 0, 0, 86, 264, 192, 0, 136, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0530_semantics :
    (Generated.hostChunk044[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[2]).mask = 43007 := by decide +kernel
  have hv : (Generated.hostChunk044[2]).primitive.toList = [26, 0, 0, 0, 0, 86, 264, 192, 0, 136, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0530]
  rfl

theorem primitive_values_0531 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43807) = [20, 10, 10, 0, 0, 50, 90, 90, 0, 50, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0531_semantics :
    (Generated.hostChunk044[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[3]).mask = 43807 := by decide +kernel
  have hv : (Generated.hostChunk044[3]).primitive.toList = [20, 10, 10, 0, 0, 50, 90, 90, 0, 50, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0531]
  rfl

theorem primitive_values_0532 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43814) = [16, 10, 4, 0, 4, 24, 18, 30, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0532_semantics :
    (Generated.hostChunk044[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[4]).mask = 43814 := by decide +kernel
  have hv : (Generated.hostChunk044[4]).primitive.toList = [16, 10, 4, 0, 4, 24, 18, 30, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0532]
  rfl

theorem primitive_values_0533 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43815) = [18, 10, 6, 0, 6, 34, 42, 54, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0533_semantics :
    (Generated.hostChunk044[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[5]).mask = 43815 := by decide +kernel
  have hv : (Generated.hostChunk044[5]).primitive.toList = [18, 10, 6, 0, 6, 34, 42, 54, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0533]
  rfl

theorem primitive_values_0534 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43821) = [18, 20, 14, 4, 6, 34, 42, 50, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0534_semantics :
    (Generated.hostChunk044[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[6]).mask = 43821 := by decide +kernel
  have hv : (Generated.hostChunk044[6]).primitive.toList = [18, 20, 14, 4, 6, 34, 42, 50, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0534]
  rfl

theorem primitive_values_0535 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43823) = [20, 10, 8, 0, 8, 46, 84, 78, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0535_semantics :
    (Generated.hostChunk044[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[7]).mask = 43823 := by decide +kernel
  have hv : (Generated.hostChunk044[7]).primitive.toList = [20, 10, 8, 0, 8, 46, 84, 78, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0535]
  rfl

theorem primitive_values_0536 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43839) = [22, 10, 10, 0, 10, 60, 150, 110, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0536_semantics :
    (Generated.hostChunk044[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[8]).mask = 43839 := by decide +kernel
  have hv : (Generated.hostChunk044[8]).primitive.toList = [22, 10, 10, 0, 10, 60, 150, 110, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0536]
  rfl

theorem primitive_values_0537 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43868) = [18, 0, 0, 0, 0, 36, 36, 60, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0537_semantics :
    (Generated.hostChunk044[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[9]).mask = 43868 := by decide +kernel
  have hv : (Generated.hostChunk044[9]).primitive.toList = [18, 0, 0, 0, 0, 36, 36, 60, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0537]
  rfl

theorem primitive_values_0538 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43869) = [20, 0, 0, 0, 0, 48, 72, 90, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0538_semantics :
    (Generated.hostChunk044[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[10]).mask = 43869 := by decide +kernel
  have hv : (Generated.hostChunk044[10]).primitive.toList = [20, 0, 0, 0, 0, 48, 72, 90, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0538]
  rfl

theorem primitive_values_0539 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43871) = [22, 0, 0, 0, 0, 62, 126, 128, 0, 82, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0539_semantics :
    (Generated.hostChunk044[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk044[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk044[11]).mask = 43871 := by decide +kernel
  have hv : (Generated.hostChunk044[11]).primitive.toList = [22, 0, 0, 0, 0, 62, 126, 128, 0, 82, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0539]
  rfl

theorem primitive_chunk_044_semantics :
    ∀ h ∈ Generated.hostChunk044.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk044.toList = [Generated.hostChunk044[0], Generated.hostChunk044[1], Generated.hostChunk044[2], Generated.hostChunk044[3], Generated.hostChunk044[4], Generated.hostChunk044[5], Generated.hostChunk044[6], Generated.hostChunk044[7], Generated.hostChunk044[8], Generated.hostChunk044[9], Generated.hostChunk044[10], Generated.hostChunk044[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0528_semantics
  · exact primitive_host_0529_semantics
  · exact primitive_host_0530_semantics
  · exact primitive_host_0531_semantics
  · exact primitive_host_0532_semantics
  · exact primitive_host_0533_semantics
  · exact primitive_host_0534_semantics
  · exact primitive_host_0535_semantics
  · exact primitive_host_0536_semantics
  · exact primitive_host_0537_semantics
  · exact primitive_host_0538_semantics
  · exact primitive_host_0539_semantics

end InducedPentagons.Paper

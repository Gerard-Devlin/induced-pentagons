import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData037
import InducedPentagonsPaper.Generated.PrimitiveRows029

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0444 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39923) = [22, 0, 0, 0, 0, 58, 120, 108, 0, 66, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0444_semantics :
    (Generated.hostChunk037[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[0]).mask = 39923 := by decide +kernel
  have hv : (Generated.hostChunk037[0]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 108, 0, 66, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0444]
  rfl

theorem primitive_values_0445 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39926) = [22, 0, 0, 0, 0, 56, 102, 108, 0, 54, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0445_semantics :
    (Generated.hostChunk037[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[1]).mask = 39926 := by decide +kernel
  have hv : (Generated.hostChunk037[1]).primitive.toList = [22, 0, 0, 0, 0, 56, 102, 108, 0, 54, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0445]
  rfl

theorem primitive_values_0446 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39927) = [24, 0, 0, 0, 0, 72, 174, 154, 0, 106, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0446_semantics :
    (Generated.hostChunk037[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[2]).mask = 39927 := by decide +kernel
  have hv : (Generated.hostChunk037[2]).primitive.toList = [24, 0, 0, 0, 0, 72, 174, 154, 0, 106, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0446]
  rfl

theorem primitive_values_0447 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39934) = [24, 0, 0, 0, 0, 70, 156, 152, 0, 90, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0447_semantics :
    (Generated.hostChunk037[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[3]).mask = 39934 := by decide +kernel
  have hv : (Generated.hostChunk037[3]).primitive.toList = [24, 0, 0, 0, 0, 70, 156, 152, 0, 90, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0447]
  rfl

theorem primitive_values_0448 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39935) = [26, 0, 0, 0, 0, 88, 252, 208, 0, 170, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by
  decide +kernel

theorem primitive_host_0448_semantics :
    (Generated.hostChunk037[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[4]).mask = 39935 := by decide +kernel
  have hv : (Generated.hostChunk037[4]).primitive.toList = [26, 0, 0, 0, 0, 88, 252, 208, 0, 170, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by decide +kernel
  rw [hm, hv, primitive_values_0448]
  rfl

theorem primitive_values_0449 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40496) = [14, 0, 0, 0, 0, 14, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0449_semantics :
    (Generated.hostChunk037[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[5]).mask = 40496 := by decide +kernel
  have hv : (Generated.hostChunk037[5]).primitive.toList = [14, 0, 0, 0, 0, 14, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0449]
  rfl

theorem primitive_values_0450 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40497) = [16, 0, 0, 0, 0, 22, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0450_semantics :
    (Generated.hostChunk037[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[6]).mask = 40497 := by decide +kernel
  have hv : (Generated.hostChunk037[6]).primitive.toList = [16, 0, 0, 0, 0, 22, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0450]
  rfl

theorem primitive_values_0451 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40498) = [16, 0, 0, 0, 0, 22, 12, 24, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0451_semantics :
    (Generated.hostChunk037[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[7]).mask = 40498 := by decide +kernel
  have hv : (Generated.hostChunk037[7]).primitive.toList = [16, 0, 0, 0, 0, 22, 12, 24, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0451]
  rfl

theorem primitive_values_0452 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40499) = [18, 0, 0, 0, 0, 32, 36, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0452_semantics :
    (Generated.hostChunk037[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[8]).mask = 40499 := by decide +kernel
  have hv : (Generated.hostChunk037[8]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0452]
  rfl

theorem primitive_values_0453 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40502) = [18, 0, 0, 0, 0, 32, 36, 44, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0453_semantics :
    (Generated.hostChunk037[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[9]).mask = 40502 := by decide +kernel
  have hv : (Generated.hostChunk037[9]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 44, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0453]
  rfl

theorem primitive_values_0454 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40503) = [20, 0, 0, 0, 0, 44, 78, 64, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0454_semantics :
    (Generated.hostChunk037[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[10]).mask = 40503 := by decide +kernel
  have hv : (Generated.hostChunk037[10]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 64, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0454]
  rfl

theorem primitive_values_0455 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40510) = [20, 0, 0, 0, 0, 44, 78, 68, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0455_semantics :
    (Generated.hostChunk037[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk037[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk037[11]).mask = 40510 := by decide +kernel
  have hv : (Generated.hostChunk037[11]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 68, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0455]
  rfl

theorem primitive_chunk_037_semantics :
    ∀ h ∈ Generated.hostChunk037.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk037.toList = [Generated.hostChunk037[0], Generated.hostChunk037[1], Generated.hostChunk037[2], Generated.hostChunk037[3], Generated.hostChunk037[4], Generated.hostChunk037[5], Generated.hostChunk037[6], Generated.hostChunk037[7], Generated.hostChunk037[8], Generated.hostChunk037[9], Generated.hostChunk037[10], Generated.hostChunk037[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0444_semantics
  · exact primitive_host_0445_semantics
  · exact primitive_host_0446_semantics
  · exact primitive_host_0447_semantics
  · exact primitive_host_0448_semantics
  · exact primitive_host_0449_semantics
  · exact primitive_host_0450_semantics
  · exact primitive_host_0451_semantics
  · exact primitive_host_0452_semantics
  · exact primitive_host_0453_semantics
  · exact primitive_host_0454_semantics
  · exact primitive_host_0455_semantics

end InducedPentagons.Paper

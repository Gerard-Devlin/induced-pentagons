import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData036
import InducedPentagonsPaper.Generated.PrimitiveRows028

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0432 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39673) = [20, 0, 0, 0, 0, 44, 66, 72, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0432_semantics :
    (Generated.hostChunk036[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[0]).mask = 39673 := by decide +kernel
  have hv : (Generated.hostChunk036[0]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 72, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0432]
  rfl

theorem primitive_values_0433 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39674) = [20, 10, 10, 4, 0, 44, 66, 74, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0433_semantics :
    (Generated.hostChunk036[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[1]).mask = 39674 := by decide +kernel
  have hv : (Generated.hostChunk036[1]).primitive.toList = [20, 10, 10, 4, 0, 44, 66, 74, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0433]
  rfl

theorem primitive_values_0434 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39675) = [22, 0, 0, 0, 0, 58, 120, 110, 0, 54, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0434_semantics :
    (Generated.hostChunk036[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[2]).mask = 39675 := by decide +kernel
  have hv : (Generated.hostChunk036[2]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 110, 0, 54, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0434]
  rfl

theorem primitive_values_0435 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39678) = [22, 0, 0, 0, 0, 58, 120, 112, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0435_semantics :
    (Generated.hostChunk036[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[3]).mask = 39678 := by decide +kernel
  have hv : (Generated.hostChunk036[3]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 112, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0435]
  rfl

theorem primitive_values_0436 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39679) = [24, 0, 0, 0, 0, 74, 198, 156, 0, 110, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0436_semantics :
    (Generated.hostChunk036[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[4]).mask = 39679 := by decide +kernel
  have hv : (Generated.hostChunk036[4]).primitive.toList = [24, 0, 0, 0, 0, 74, 198, 156, 0, 110, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0436]
  rfl

theorem primitive_values_0437 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39902) = [22, 0, 0, 0, 0, 62, 120, 132, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0437_semantics :
    (Generated.hostChunk036[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[5]).mask = 39902 := by decide +kernel
  have hv : (Generated.hostChunk036[5]).primitive.toList = [22, 0, 0, 0, 0, 62, 120, 132, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0437]
  rfl

theorem primitive_values_0438 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39903) = [24, 0, 0, 0, 0, 78, 192, 180, 0, 156, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by
  decide +kernel

theorem primitive_host_0438_semantics :
    (Generated.hostChunk036[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[6]).mask = 39903 := by decide +kernel
  have hv : (Generated.hostChunk036[6]).primitive.toList = [24, 0, 0, 0, 0, 78, 192, 180, 0, 156, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by decide +kernel
  rw [hm, hv, primitive_values_0438]
  rfl

theorem primitive_values_0439 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39918) = [22, 0, 0, 0, 0, 60, 120, 120, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0439_semantics :
    (Generated.hostChunk036[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[7]).mask = 39918 := by decide +kernel
  have hv : (Generated.hostChunk036[7]).primitive.toList = [22, 0, 0, 0, 0, 60, 120, 120, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0439]
  rfl

theorem primitive_values_0440 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39919) = [24, 0, 0, 0, 0, 76, 192, 170, 0, 144, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0440_semantics :
    (Generated.hostChunk036[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[8]).mask = 39919 := by decide +kernel
  have hv : (Generated.hostChunk036[8]).primitive.toList = [24, 0, 0, 0, 0, 76, 192, 170, 0, 144, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0440]
  rfl

theorem primitive_values_0441 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39920) = [18, 0, 0, 0, 0, 34, 42, 44, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0441_semantics :
    (Generated.hostChunk036[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[9]).mask = 39920 := by decide +kernel
  have hv : (Generated.hostChunk036[9]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 44, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0441]
  rfl

theorem primitive_values_0442 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39921) = [20, 0, 0, 0, 0, 46, 84, 70, 0, 44, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0442_semantics :
    (Generated.hostChunk036[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[10]).mask = 39921 := by decide +kernel
  have hv : (Generated.hostChunk036[10]).primitive.toList = [20, 0, 0, 0, 0, 46, 84, 70, 0, 44, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0442]
  rfl

theorem primitive_values_0443 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39922) = [20, 0, 0, 0, 0, 44, 66, 72, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0443_semantics :
    (Generated.hostChunk036[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk036[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk036[11]).mask = 39922 := by decide +kernel
  have hv : (Generated.hostChunk036[11]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 72, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0443]
  rfl

theorem primitive_chunk_036_semantics :
    ∀ h ∈ Generated.hostChunk036.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk036.toList = [Generated.hostChunk036[0], Generated.hostChunk036[1], Generated.hostChunk036[2], Generated.hostChunk036[3], Generated.hostChunk036[4], Generated.hostChunk036[5], Generated.hostChunk036[6], Generated.hostChunk036[7], Generated.hostChunk036[8], Generated.hostChunk036[9], Generated.hostChunk036[10], Generated.hostChunk036[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0432_semantics
  · exact primitive_host_0433_semantics
  · exact primitive_host_0434_semantics
  · exact primitive_host_0435_semantics
  · exact primitive_host_0436_semantics
  · exact primitive_host_0437_semantics
  · exact primitive_host_0438_semantics
  · exact primitive_host_0439_semantics
  · exact primitive_host_0440_semantics
  · exact primitive_host_0441_semantics
  · exact primitive_host_0442_semantics
  · exact primitive_host_0443_semantics

end InducedPentagons.Paper

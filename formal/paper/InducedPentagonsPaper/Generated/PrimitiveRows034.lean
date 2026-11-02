import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData034
import InducedPentagonsPaper.Generated.PrimitiveRows026

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0408 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39542) = [18, 0, 0, 0, 0, 36, 54, 54, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0408_semantics :
    (Generated.hostChunk034[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[0]).mask = 39542 := by decide +kernel
  have hv : (Generated.hostChunk034[0]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 54, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0408]
  rfl

theorem primitive_values_0409 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39543) = [20, 0, 0, 0, 0, 48, 96, 78, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0409_semantics :
    (Generated.hostChunk034[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[1]).mask = 39543 := by decide +kernel
  have hv : (Generated.hostChunk034[1]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 78, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0409]
  rfl

theorem primitive_values_0410 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39548) = [18, 20, 16, 8, 0, 34, 42, 48, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0410_semantics :
    (Generated.hostChunk034[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[2]).mask = 39548 := by decide +kernel
  have hv : (Generated.hostChunk034[2]).primitive.toList = [18, 20, 16, 8, 0, 34, 42, 48, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0410]
  rfl

theorem primitive_values_0411 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39549) = [20, 0, 0, 0, 0, 46, 84, 74, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0411_semantics :
    (Generated.hostChunk034[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[3]).mask = 39549 := by decide +kernel
  have hv : (Generated.hostChunk034[3]).primitive.toList = [20, 0, 0, 0, 0, 46, 84, 74, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0411]
  rfl

theorem primitive_values_0412 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39550) = [20, 0, 0, 0, 0, 48, 96, 80, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0412_semantics :
    (Generated.hostChunk034[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[4]).mask = 39550 := by decide +kernel
  have hv : (Generated.hostChunk034[4]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 80, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0412]
  rfl

theorem primitive_values_0413 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39551) = [22, 0, 0, 0, 0, 62, 162, 112, 0, 72, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0413_semantics :
    (Generated.hostChunk034[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[5]).mask = 39551 := by decide +kernel
  have hv : (Generated.hostChunk034[5]).primitive.toList = [22, 0, 0, 0, 0, 62, 162, 112, 0, 72, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0413]
  rfl

theorem primitive_values_0414 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39639) = [20, 0, 0, 0, 0, 52, 96, 96, 0, 64, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0414_semantics :
    (Generated.hostChunk034[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[6]).mask = 39639 := by decide +kernel
  have hv : (Generated.hostChunk034[6]).primitive.toList = [20, 0, 0, 0, 0, 52, 96, 96, 0, 64, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0414]
  rfl

theorem primitive_values_0415 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39642) = [18, 10, 8, 0, 0, 38, 48, 62, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0415_semantics :
    (Generated.hostChunk034[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[7]).mask = 39642 := by decide +kernel
  have hv : (Generated.hostChunk034[7]).primitive.toList = [18, 10, 8, 0, 0, 38, 48, 62, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0415]
  rfl

theorem primitive_values_0416 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39643) = [20, 0, 0, 0, 0, 50, 84, 92, 0, 48, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0416_semantics :
    (Generated.hostChunk034[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[8]).mask = 39643 := by decide +kernel
  have hv : (Generated.hostChunk034[8]).primitive.toList = [20, 0, 0, 0, 0, 50, 84, 92, 0, 48, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0416]
  rfl

theorem primitive_values_0417 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39646) = [20, 0, 0, 0, 0, 50, 84, 94, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0417_semantics :
    (Generated.hostChunk034[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[9]).mask = 39646 := by decide +kernel
  have hv : (Generated.hostChunk034[9]).primitive.toList = [20, 0, 0, 0, 0, 50, 84, 94, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0417]
  rfl

theorem primitive_values_0418 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39647) = [22, 0, 0, 0, 0, 64, 138, 132, 0, 98, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0418_semantics :
    (Generated.hostChunk034[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[10]).mask = 39647 := by decide +kernel
  have hv : (Generated.hostChunk034[10]).primitive.toList = [22, 0, 0, 0, 0, 64, 138, 132, 0, 98, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0418]
  rfl

theorem primitive_values_0419 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39654) = [18, 0, 0, 0, 0, 38, 60, 60, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0419_semantics :
    (Generated.hostChunk034[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk034[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk034[11]).mask = 39654 := by decide +kernel
  have hv : (Generated.hostChunk034[11]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 60, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0419]
  rfl

theorem primitive_chunk_034_semantics :
    ∀ h ∈ Generated.hostChunk034.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk034.toList = [Generated.hostChunk034[0], Generated.hostChunk034[1], Generated.hostChunk034[2], Generated.hostChunk034[3], Generated.hostChunk034[4], Generated.hostChunk034[5], Generated.hostChunk034[6], Generated.hostChunk034[7], Generated.hostChunk034[8], Generated.hostChunk034[9], Generated.hostChunk034[10], Generated.hostChunk034[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0408_semantics
  · exact primitive_host_0409_semantics
  · exact primitive_host_0410_semantics
  · exact primitive_host_0411_semantics
  · exact primitive_host_0412_semantics
  · exact primitive_host_0413_semantics
  · exact primitive_host_0414_semantics
  · exact primitive_host_0415_semantics
  · exact primitive_host_0416_semantics
  · exact primitive_host_0417_semantics
  · exact primitive_host_0418_semantics
  · exact primitive_host_0419_semantics

end InducedPentagons.Paper

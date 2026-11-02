import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData009
import InducedPentagonsPaper.Generated.PrimitiveRows001

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0108 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2519) = [16, 0, 0, 0, 0, 36, 60, 50, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0108_semantics :
    (Generated.hostChunk009[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[0]).mask = 2519 := by decide +kernel
  have hv : (Generated.hostChunk009[0]).primitive.toList = [16, 0, 0, 0, 0, 36, 60, 50, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0108]
  rfl

theorem primitive_values_0109 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2520) = [12, 0, 0, 0, 0, 14, 6, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0109_semantics :
    (Generated.hostChunk009[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[1]).mask = 2520 := by decide +kernel
  have hv : (Generated.hostChunk009[1]).primitive.toList = [12, 0, 0, 0, 0, 14, 6, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0109]
  rfl

theorem primitive_values_0110 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2521) = [14, 0, 0, 0, 0, 24, 30, 24, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0110_semantics :
    (Generated.hostChunk009[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[2]).mask = 2521 := by decide +kernel
  have hv : (Generated.hostChunk009[2]).primitive.toList = [14, 0, 0, 0, 0, 24, 30, 24, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0110]
  rfl

theorem primitive_values_0111 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2522) = [14, 0, 0, 0, 0, 22, 18, 26, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0111_semantics :
    (Generated.hostChunk009[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[3]).mask = 2522 := by decide +kernel
  have hv : (Generated.hostChunk009[3]).primitive.toList = [14, 0, 0, 0, 0, 22, 18, 26, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0111]
  rfl

theorem primitive_values_0112 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2523) = [16, 0, 0, 0, 0, 34, 54, 46, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0112_semantics :
    (Generated.hostChunk009[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[4]).mask = 2523 := by decide +kernel
  have hv : (Generated.hostChunk009[4]).primitive.toList = [16, 0, 0, 0, 0, 34, 54, 46, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0112]
  rfl

theorem primitive_values_0113 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2526) = [16, 0, 0, 0, 0, 32, 42, 46, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0113_semantics :
    (Generated.hostChunk009[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[5]).mask = 2526 := by decide +kernel
  have hv : (Generated.hostChunk009[5]).primitive.toList = [16, 0, 0, 0, 0, 32, 42, 46, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0113]
  rfl

theorem primitive_values_0114 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2527) = [18, 0, 0, 0, 0, 46, 96, 72, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0114_semantics :
    (Generated.hostChunk009[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[6]).mask = 2527 := by decide +kernel
  have hv : (Generated.hostChunk009[6]).primitive.toList = [18, 0, 0, 0, 0, 46, 96, 72, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0114]
  rfl

theorem primitive_values_0115 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2544) = [12, 0, 0, 0, 0, 12, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0115_semantics :
    (Generated.hostChunk009[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[7]).mask = 2544 := by decide +kernel
  have hv : (Generated.hostChunk009[7]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0115]
  rfl

theorem primitive_values_0116 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2545) = [14, 0, 0, 0, 0, 22, 30, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0116_semantics :
    (Generated.hostChunk009[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[8]).mask = 2545 := by decide +kernel
  have hv : (Generated.hostChunk009[8]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0116]
  rfl

theorem primitive_values_0117 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2546) = [14, 0, 0, 0, 0, 20, 18, 18, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0117_semantics :
    (Generated.hostChunk009[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[9]).mask = 2546 := by decide +kernel
  have hv : (Generated.hostChunk009[9]).primitive.toList = [14, 0, 0, 0, 0, 20, 18, 18, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0117]
  rfl

theorem primitive_values_0118 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2547) = [16, 0, 0, 0, 0, 32, 54, 40, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0118_semantics :
    (Generated.hostChunk009[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[10]).mask = 2547 := by decide +kernel
  have hv : (Generated.hostChunk009[10]).primitive.toList = [16, 0, 0, 0, 0, 32, 54, 40, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0118]
  rfl

theorem primitive_values_0119 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2550) = [16, 0, 0, 0, 0, 30, 42, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0119_semantics :
    (Generated.hostChunk009[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk009[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk009[11]).mask = 2550 := by decide +kernel
  have hv : (Generated.hostChunk009[11]).primitive.toList = [16, 0, 0, 0, 0, 30, 42, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0119]
  rfl

theorem primitive_chunk_009_semantics :
    ∀ h ∈ Generated.hostChunk009.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk009.toList = [Generated.hostChunk009[0], Generated.hostChunk009[1], Generated.hostChunk009[2], Generated.hostChunk009[3], Generated.hostChunk009[4], Generated.hostChunk009[5], Generated.hostChunk009[6], Generated.hostChunk009[7], Generated.hostChunk009[8], Generated.hostChunk009[9], Generated.hostChunk009[10], Generated.hostChunk009[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0108_semantics
  · exact primitive_host_0109_semantics
  · exact primitive_host_0110_semantics
  · exact primitive_host_0111_semantics
  · exact primitive_host_0112_semantics
  · exact primitive_host_0113_semantics
  · exact primitive_host_0114_semantics
  · exact primitive_host_0115_semantics
  · exact primitive_host_0116_semantics
  · exact primitive_host_0117_semantics
  · exact primitive_host_0118_semantics
  · exact primitive_host_0119_semantics

end InducedPentagons.Paper

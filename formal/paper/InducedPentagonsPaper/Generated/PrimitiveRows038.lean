import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData038
import InducedPentagonsPaper.Generated.PrimitiveRows030

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0456 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40511) = [22, 0, 0, 0, 0, 58, 144, 96, 0, 62, 4, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0456_semantics :
    (Generated.hostChunk038[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[0]).mask = 40511 := by decide +kernel
  have hv : (Generated.hostChunk038[0]).primitive.toList = [22, 0, 0, 0, 0, 58, 144, 96, 0, 62, 4, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0456]
  rfl

theorem primitive_values_0457 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40562) = [18, 0, 0, 0, 0, 32, 36, 48, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0457_semantics :
    (Generated.hostChunk038[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[1]).mask = 40562 := by decide +kernel
  have hv : (Generated.hostChunk038[1]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 48, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0457]
  rfl

theorem primitive_values_0458 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40563) = [20, 0, 0, 0, 0, 44, 72, 68, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0458_semantics :
    (Generated.hostChunk038[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[2]).mask = 40563 := by decide +kernel
  have hv : (Generated.hostChunk038[2]).primitive.toList = [20, 0, 0, 0, 0, 44, 72, 68, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0458]
  rfl

theorem primitive_values_0459 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40564) = [18, 20, 16, 0, 0, 30, 24, 42, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0459_semantics :
    (Generated.hostChunk038[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[3]).mask = 40564 := by decide +kernel
  have hv : (Generated.hostChunk038[3]).primitive.toList = [18, 20, 16, 0, 0, 30, 24, 42, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0459]
  rfl

theorem primitive_values_0460 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40565) = [20, 0, 0, 0, 0, 42, 60, 64, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0460_semantics :
    (Generated.hostChunk038[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[4]).mask = 40565 := by decide +kernel
  have hv : (Generated.hostChunk038[4]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 64, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0460]
  rfl

theorem primitive_values_0461 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40566) = [20, 0, 0, 0, 0, 42, 60, 72, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0461_semantics :
    (Generated.hostChunk038[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[5]).mask = 40566 := by decide +kernel
  have hv : (Generated.hostChunk038[5]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 72, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0461]
  rfl

theorem primitive_values_0462 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40567) = [22, 0, 0, 0, 0, 56, 114, 102, 0, 52, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0462_semantics :
    (Generated.hostChunk038[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[6]).mask = 40567 := by decide +kernel
  have hv : (Generated.hostChunk038[6]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 102, 0, 52, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0462]
  rfl

theorem primitive_values_0463 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40572) = [20, 40, 40, 16, 0, 40, 48, 64, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0463_semantics :
    (Generated.hostChunk038[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[7]).mask = 40572 := by decide +kernel
  have hv : (Generated.hostChunk038[7]).primitive.toList = [20, 40, 40, 16, 0, 40, 48, 64, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0463]
  rfl

theorem primitive_values_0464 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40573) = [22, 0, 0, 0, 0, 54, 102, 96, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0464_semantics :
    (Generated.hostChunk038[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[8]).mask = 40573 := by decide +kernel
  have hv : (Generated.hostChunk038[8]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 96, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0464]
  rfl

theorem primitive_values_0465 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40574) = [22, 0, 0, 0, 0, 54, 102, 100, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0465_semantics :
    (Generated.hostChunk038[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[9]).mask = 40574 := by decide +kernel
  have hv : (Generated.hostChunk038[9]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 100, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0465]
  rfl

theorem primitive_values_0466 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40575) = [24, 0, 0, 0, 0, 70, 180, 140, 0, 88, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0466_semantics :
    (Generated.hostChunk038[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[10]).mask = 40575 := by decide +kernel
  have hv : (Generated.hostChunk038[10]).primitive.toList = [24, 0, 0, 0, 0, 70, 180, 140, 0, 88, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0466]
  rfl

theorem primitive_values_0467 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40694) = [22, 0, 0, 0, 0, 54, 96, 108, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0467_semantics :
    (Generated.hostChunk038[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk038[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk038[11]).mask = 40694 := by decide +kernel
  have hv : (Generated.hostChunk038[11]).primitive.toList = [22, 0, 0, 0, 0, 54, 96, 108, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0467]
  rfl

theorem primitive_chunk_038_semantics :
    ∀ h ∈ Generated.hostChunk038.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk038.toList = [Generated.hostChunk038[0], Generated.hostChunk038[1], Generated.hostChunk038[2], Generated.hostChunk038[3], Generated.hostChunk038[4], Generated.hostChunk038[5], Generated.hostChunk038[6], Generated.hostChunk038[7], Generated.hostChunk038[8], Generated.hostChunk038[9], Generated.hostChunk038[10], Generated.hostChunk038[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0456_semantics
  · exact primitive_host_0457_semantics
  · exact primitive_host_0458_semantics
  · exact primitive_host_0459_semantics
  · exact primitive_host_0460_semantics
  · exact primitive_host_0461_semantics
  · exact primitive_host_0462_semantics
  · exact primitive_host_0463_semantics
  · exact primitive_host_0464_semantics
  · exact primitive_host_0465_semantics
  · exact primitive_host_0466_semantics
  · exact primitive_host_0467_semantics

end InducedPentagons.Paper

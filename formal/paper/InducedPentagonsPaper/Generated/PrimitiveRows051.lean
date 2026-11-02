import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData051
import InducedPentagonsPaper.Generated.PrimitiveRows043

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0612 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44527) = [24, 0, 0, 0, 0, 72, 174, 158, 0, 110, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0612_semantics :
    (Generated.hostChunk051[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[0]).mask = 44527 := by decide +kernel
  have hv : (Generated.hostChunk051[0]).primitive.toList = [24, 0, 0, 0, 0, 72, 174, 158, 0, 110, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0612]
  rfl

theorem primitive_values_0613 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44534) = [22, 0, 0, 0, 0, 54, 96, 102, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0613_semantics :
    (Generated.hostChunk051[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[1]).mask = 44534 := by decide +kernel
  have hv : (Generated.hostChunk051[1]).primitive.toList = [22, 0, 0, 0, 0, 54, 96, 102, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0613]
  rfl

theorem primitive_values_0614 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44535) = [24, 0, 0, 0, 0, 70, 168, 148, 0, 92, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0614_semantics :
    (Generated.hostChunk051[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[2]).mask = 44535 := by decide +kernel
  have hv : (Generated.hostChunk051[2]).primitive.toList = [24, 0, 0, 0, 0, 70, 168, 148, 0, 92, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0614]
  rfl

theorem primitive_values_0615 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44536) = [20, 30, 26, 8, 16, 40, 48, 66, 4, 16, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0615_semantics :
    (Generated.hostChunk051[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[3]).mask = 44536 := by decide +kernel
  have hv : (Generated.hostChunk051[3]).primitive.toList = [20, 30, 26, 8, 16, 40, 48, 66, 4, 16, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0615]
  rfl

theorem primitive_values_0616 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44537) = [22, 10, 10, 4, 10, 54, 102, 100, 4, 42, 12, 0, 0, 0, 0, 0, 4, 2, 1, 1, 0, 12] := by
  decide +kernel

theorem primitive_host_0616_semantics :
    (Generated.hostChunk051[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[4]).mask = 44537 := by decide +kernel
  have hv : (Generated.hostChunk051[4]).primitive.toList = [22, 10, 10, 4, 10, 54, 102, 100, 4, 42, 12, 0, 0, 0, 0, 0, 4, 2, 1, 1, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0616]
  rfl

theorem primitive_values_0617 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44538) = [22, 0, 0, 0, 0, 52, 84, 98, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0617_semantics :
    (Generated.hostChunk051[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[5]).mask = 44538 := by decide +kernel
  have hv : (Generated.hostChunk051[5]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 98, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0617]
  rfl

theorem primitive_values_0618 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44539) = [24, 0, 0, 0, 0, 68, 156, 142, 0, 74, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0618_semantics :
    (Generated.hostChunk051[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[6]).mask = 44539 := by decide +kernel
  have hv : (Generated.hostChunk051[6]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 142, 0, 74, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0618]
  rfl

theorem primitive_values_0619 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44540) = [22, 20, 22, 16, 10, 52, 84, 100, 8, 30, 8, 0, 0, 0, 0, 0, 8, 6, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0619_semantics :
    (Generated.hostChunk051[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[7]).mask = 44540 := by decide +kernel
  have hv : (Generated.hostChunk051[7]).primitive.toList = [22, 20, 22, 16, 10, 52, 84, 100, 8, 30, 8, 0, 0, 0, 0, 0, 8, 6, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0619]
  rfl

theorem primitive_values_0620 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44541) = [24, 0, 0, 0, 0, 68, 156, 144, 0, 78, 16, 0, 4, 24, 0, 4, 0, 0, 3, 3, 0, 40] := by
  decide +kernel

theorem primitive_host_0620_semantics :
    (Generated.hostChunk051[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[8]).mask = 44541 := by decide +kernel
  have hv : (Generated.hostChunk051[8]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 144, 0, 78, 16, 0, 4, 24, 0, 4, 0, 0, 3, 3, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0620]
  rfl

theorem primitive_values_0621 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44542) = [24, 0, 0, 0, 0, 66, 138, 140, 0, 58, 20, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 20] := by
  decide +kernel

theorem primitive_host_0621_semantics :
    (Generated.hostChunk051[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[9]).mask = 44542 := by decide +kernel
  have hv : (Generated.hostChunk051[9]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 140, 0, 58, 20, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0621]
  rfl

theorem primitive_values_0622 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44543) = [26, 0, 0, 0, 0, 84, 234, 194, 0, 134, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 2, 80] := by
  decide +kernel

theorem primitive_host_0622_semantics :
    (Generated.hostChunk051[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[10]).mask = 44543 := by decide +kernel
  have hv : (Generated.hostChunk051[10]).primitive.toList = [26, 0, 0, 0, 0, 84, 234, 194, 0, 134, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 2, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0622]
  rfl

theorem primitive_values_0623 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44856) = [18, 20, 12, 0, 12, 30, 24, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0623_semantics :
    (Generated.hostChunk051[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk051[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk051[11]).mask = 44856 := by decide +kernel
  have hv : (Generated.hostChunk051[11]).primitive.toList = [18, 20, 12, 0, 12, 30, 24, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0623]
  rfl

theorem primitive_chunk_051_semantics :
    ∀ h ∈ Generated.hostChunk051.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk051.toList = [Generated.hostChunk051[0], Generated.hostChunk051[1], Generated.hostChunk051[2], Generated.hostChunk051[3], Generated.hostChunk051[4], Generated.hostChunk051[5], Generated.hostChunk051[6], Generated.hostChunk051[7], Generated.hostChunk051[8], Generated.hostChunk051[9], Generated.hostChunk051[10], Generated.hostChunk051[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0612_semantics
  · exact primitive_host_0613_semantics
  · exact primitive_host_0614_semantics
  · exact primitive_host_0615_semantics
  · exact primitive_host_0616_semantics
  · exact primitive_host_0617_semantics
  · exact primitive_host_0618_semantics
  · exact primitive_host_0619_semantics
  · exact primitive_host_0620_semantics
  · exact primitive_host_0621_semantics
  · exact primitive_host_0622_semantics
  · exact primitive_host_0623_semantics

end InducedPentagons.Paper

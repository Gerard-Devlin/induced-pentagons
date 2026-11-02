import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData063
import InducedPentagonsPaper.Generated.PrimitiveRows055

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0756 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59327) = [26, 0, 0, 0, 0, 80, 210, 180, 0, 110, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by
  decide +kernel

theorem primitive_host_0756_semantics :
    (Generated.hostChunk063[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[0]).mask = 59327 := by decide +kernel
  have hv : (Generated.hostChunk063[0]).primitive.toList = [26, 0, 0, 0, 0, 80, 210, 180, 0, 110, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0756]
  rfl

theorem primitive_values_0757 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59390) = [26, 0, 0, 0, 0, 76, 168, 172, 0, 68, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0757_semantics :
    (Generated.hostChunk063[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[1]).mask = 59390 := by decide +kernel
  have hv : (Generated.hostChunk063[1]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 172, 0, 68, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0757]
  rfl

theorem primitive_values_0758 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59391) = [28, 0, 0, 0, 0, 96, 288, 236, 0, 172, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0758_semantics :
    (Generated.hostChunk063[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[2]).mask = 59391 := by decide +kernel
  have hv : (Generated.hostChunk063[2]).primitive.toList = [28, 0, 0, 0, 0, 96, 288, 236, 0, 172, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0758]
  rfl

theorem primitive_values_0759 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61111) = [24, 0, 0, 0, 0, 68, 144, 152, 0, 76, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0759_semantics :
    (Generated.hostChunk063[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[3]).mask = 61111 := by decide +kernel
  have hv : (Generated.hostChunk063[3]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 152, 0, 76, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0759]
  rfl

theorem primitive_values_0760 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61112) = [20, 40, 32, 0, 32, 38, 36, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0760_semantics :
    (Generated.hostChunk063[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[4]).mask = 61112 := by decide +kernel
  have hv : (Generated.hostChunk063[4]).primitive.toList = [20, 40, 32, 0, 32, 38, 36, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0760]
  rfl

theorem primitive_values_0761 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61113) = [22, 20, 20, 8, 20, 50, 72, 100, 8, 20, 4, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0761_semantics :
    (Generated.hostChunk063[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[5]).mask = 61113 := by decide +kernel
  have hv : (Generated.hostChunk063[5]).primitive.toList = [22, 20, 20, 8, 20, 50, 72, 100, 8, 20, 4, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0761]
  rfl

theorem primitive_values_0762 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61115) = [24, 0, 0, 0, 0, 64, 126, 140, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 16] := by
  decide +kernel

theorem primitive_host_0762_semantics :
    (Generated.hostChunk063[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[6]).mask = 61115 := by decide +kernel
  have hv : (Generated.hostChunk063[6]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 140, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0762]
  rfl

theorem primitive_values_0763 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61116) = [22, 0, 0, 0, 0, 50, 72, 104, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0763_semantics :
    (Generated.hostChunk063[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[7]).mask = 61116 := by decide +kernel
  have hv : (Generated.hostChunk063[7]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 104, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0763]
  rfl

theorem primitive_values_0764 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61117) = [24, 0, 0, 0, 0, 64, 126, 140, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0764_semantics :
    (Generated.hostChunk063[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[8]).mask = 61117 := by decide +kernel
  have hv : (Generated.hostChunk063[8]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 140, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0764]
  rfl

theorem primitive_values_0765 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61119) = [26, 0, 0, 0, 0, 80, 204, 188, 0, 100, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0765_semantics :
    (Generated.hostChunk063[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[9]).mask = 61119 := by decide +kernel
  have hv : (Generated.hostChunk063[9]).primitive.toList = [26, 0, 0, 0, 0, 80, 204, 188, 0, 100, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0765]
  rfl

theorem primitive_values_0766 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61175) = [26, 0, 0, 0, 0, 84, 216, 204, 0, 150, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0766_semantics :
    (Generated.hostChunk063[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[10]).mask = 61175 := by decide +kernel
  have hv : (Generated.hostChunk063[10]).primitive.toList = [26, 0, 0, 0, 0, 84, 216, 204, 0, 150, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0766]
  rfl

theorem primitive_values_0767 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61176) = [22, 40, 40, 16, 40, 50, 72, 96, 16, 30, 12, 0, 0, 0, 0, 0, 16, 8, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0767_semantics :
    (Generated.hostChunk063[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk063[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk063[11]).mask = 61176 := by decide +kernel
  have hv : (Generated.hostChunk063[11]).primitive.toList = [22, 40, 40, 16, 40, 50, 72, 96, 16, 30, 12, 0, 0, 0, 0, 0, 16, 8, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0767]
  rfl

theorem primitive_chunk_063_semantics :
    ∀ h ∈ Generated.hostChunk063.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk063.toList = [Generated.hostChunk063[0], Generated.hostChunk063[1], Generated.hostChunk063[2], Generated.hostChunk063[3], Generated.hostChunk063[4], Generated.hostChunk063[5], Generated.hostChunk063[6], Generated.hostChunk063[7], Generated.hostChunk063[8], Generated.hostChunk063[9], Generated.hostChunk063[10], Generated.hostChunk063[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0756_semantics
  · exact primitive_host_0757_semantics
  · exact primitive_host_0758_semantics
  · exact primitive_host_0759_semantics
  · exact primitive_host_0760_semantics
  · exact primitive_host_0761_semantics
  · exact primitive_host_0762_semantics
  · exact primitive_host_0763_semantics
  · exact primitive_host_0764_semantics
  · exact primitive_host_0765_semantics
  · exact primitive_host_0766_semantics
  · exact primitive_host_0767_semantics

end InducedPentagons.Paper

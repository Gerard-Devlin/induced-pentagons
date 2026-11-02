import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData067
import InducedPentagonsPaper.Generated.PrimitiveRows059

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0804 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111990) = [22, 10, 10, 4, 10, 50, 72, 94, 4, 26, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0804_semantics :
    (Generated.hostChunk067[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[0]).mask = 111990 := by decide +kernel
  have hv : (Generated.hostChunk067[0]).primitive.toList = [22, 10, 10, 4, 10, 50, 72, 94, 4, 26, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0804]
  rfl

theorem primitive_values_0805 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111991) = [24, 0, 0, 0, 0, 64, 126, 134, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 16] := by
  decide +kernel

theorem primitive_host_0805_semantics :
    (Generated.hostChunk067[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[1]).mask = 111991 := by decide +kernel
  have hv : (Generated.hostChunk067[1]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 134, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0805]
  rfl

theorem primitive_values_0806 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111998) = [24, 0, 0, 0, 0, 64, 126, 136, 0, 58, 20, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 20] := by
  decide +kernel

theorem primitive_host_0806_semantics :
    (Generated.hostChunk067[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[2]).mask = 111998 := by decide +kernel
  have hv : (Generated.hostChunk067[2]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 136, 0, 58, 20, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0806]
  rfl

theorem primitive_values_0807 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111999) = [26, 0, 0, 0, 0, 80, 204, 184, 0, 112, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 4, 56] := by
  decide +kernel

theorem primitive_host_0807_semantics :
    (Generated.hostChunk067[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[3]).mask = 111999 := by decide +kernel
  have hv : (Generated.hostChunk067[3]).primitive.toList = [26, 0, 0, 0, 0, 80, 204, 184, 0, 112, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 4, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0807]
  rfl

theorem primitive_values_0808 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112110) = [24, 0, 0, 0, 0, 64, 120, 144, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0808_semantics :
    (Generated.hostChunk067[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[4]).mask = 112110 := by decide +kernel
  have hv : (Generated.hostChunk067[4]).primitive.toList = [24, 0, 0, 0, 0, 64, 120, 144, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0808]
  rfl

theorem primitive_values_0809 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112111) = [26, 0, 0, 0, 0, 80, 192, 192, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0809_semantics :
    (Generated.hostChunk067[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[5]).mask = 112111 := by decide +kernel
  have hv : (Generated.hostChunk067[5]).primitive.toList = [26, 0, 0, 0, 0, 80, 192, 192, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0809]
  rfl

theorem primitive_values_0810 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112118) = [24, 0, 0, 0, 0, 62, 108, 132, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0810_semantics :
    (Generated.hostChunk067[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[6]).mask = 112118 := by decide +kernel
  have hv : (Generated.hostChunk067[6]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 132, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0810]
  rfl

theorem primitive_values_0811 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112119) = [26, 0, 0, 0, 0, 78, 180, 182, 0, 92, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0811_semantics :
    (Generated.hostChunk067[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[7]).mask = 112119 := by decide +kernel
  have hv : (Generated.hostChunk067[7]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 182, 0, 92, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0811]
  rfl

theorem primitive_values_0812 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112122) = [24, 10, 12, 8, 12, 62, 108, 134, 8, 44, 12, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0812_semantics :
    (Generated.hostChunk067[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[8]).mask = 112122 := by decide +kernel
  have hv : (Generated.hostChunk067[8]).primitive.toList = [24, 10, 12, 8, 12, 62, 108, 134, 8, 44, 12, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0812]
  rfl

theorem primitive_values_0813 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112123) = [26, 0, 0, 0, 0, 78, 180, 184, 0, 96, 24, 0, 0, 24, 0, 4, 0, 0, 2, 2, 0, 48] := by
  decide +kernel

theorem primitive_host_0813_semantics :
    (Generated.hostChunk067[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[9]).mask = 112123 := by decide +kernel
  have hv : (Generated.hostChunk067[9]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 184, 0, 96, 24, 0, 0, 24, 0, 4, 0, 0, 2, 2, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0813]
  rfl

theorem primitive_values_0814 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112126) = [26, 0, 0, 0, 0, 76, 162, 180, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 28] := by
  decide +kernel

theorem primitive_host_0814_semantics :
    (Generated.hostChunk067[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[10]).mask = 112126 := by decide +kernel
  have hv : (Generated.hostChunk067[10]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 180, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0814]
  rfl

theorem primitive_values_0815 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112127) = [28, 0, 0, 0, 0, 94, 258, 240, 0, 156, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 4, 92] := by
  decide +kernel

theorem primitive_host_0815_semantics :
    (Generated.hostChunk067[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk067[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk067[11]).mask = 112127 := by decide +kernel
  have hv : (Generated.hostChunk067[11]).primitive.toList = [28, 0, 0, 0, 0, 94, 258, 240, 0, 156, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 4, 92] := by decide +kernel
  rw [hm, hv, primitive_values_0815]
  rfl

theorem primitive_chunk_067_semantics :
    ∀ h ∈ Generated.hostChunk067.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk067.toList = [Generated.hostChunk067[0], Generated.hostChunk067[1], Generated.hostChunk067[2], Generated.hostChunk067[3], Generated.hostChunk067[4], Generated.hostChunk067[5], Generated.hostChunk067[6], Generated.hostChunk067[7], Generated.hostChunk067[8], Generated.hostChunk067[9], Generated.hostChunk067[10], Generated.hostChunk067[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0804_semantics
  · exact primitive_host_0805_semantics
  · exact primitive_host_0806_semantics
  · exact primitive_host_0807_semantics
  · exact primitive_host_0808_semantics
  · exact primitive_host_0809_semantics
  · exact primitive_host_0810_semantics
  · exact primitive_host_0811_semantics
  · exact primitive_host_0812_semantics
  · exact primitive_host_0813_semantics
  · exact primitive_host_0814_semantics
  · exact primitive_host_0815_semantics

end InducedPentagons.Paper

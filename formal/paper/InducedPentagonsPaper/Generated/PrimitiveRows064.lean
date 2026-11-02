import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData064
import InducedPentagonsPaper.Generated.PrimitiveRows056

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0768 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61177) = [24, 20, 24, 16, 24, 64, 126, 136, 16, 60, 24, 0, 0, 0, 0, 0, 16, 8, 2, 2, 0, 24] := by
  decide +kernel

theorem primitive_host_0768_semantics :
    (Generated.hostChunk064[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[0]).mask = 61177 := by decide +kernel
  have hv : (Generated.hostChunk064[0]).primitive.toList = [24, 20, 24, 16, 24, 64, 126, 136, 16, 60, 24, 0, 0, 0, 0, 0, 16, 8, 2, 2, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0768]
  rfl

theorem primitive_values_0769 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61179) = [26, 0, 0, 0, 0, 80, 198, 188, 0, 116, 24, 0, 0, 48, 0, 16, 0, 0, 8, 8, 0, 72] := by
  decide +kernel

theorem primitive_host_0769_semantics :
    (Generated.hostChunk064[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[1]).mask = 61179 := by decide +kernel
  have hv : (Generated.hostChunk064[1]).primitive.toList = [26, 0, 0, 0, 0, 80, 198, 188, 0, 116, 24, 0, 0, 48, 0, 16, 0, 0, 8, 8, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0769]
  rfl

theorem primitive_values_0770 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61180) = [24, 0, 0, 0, 0, 62, 108, 132, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0770_semantics :
    (Generated.hostChunk064[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[2]).mask = 61180 := by decide +kernel
  have hv : (Generated.hostChunk064[2]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 132, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0770]
  rfl

theorem primitive_values_0771 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61181) = [26, 0, 0, 0, 0, 78, 180, 182, 0, 92, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0771_semantics :
    (Generated.hostChunk064[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[3]).mask = 61181 := by decide +kernel
  have hv : (Generated.hostChunk064[3]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 182, 0, 92, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0771]
  rfl

theorem primitive_values_0772 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61183) = [28, 0, 0, 0, 0, 96, 276, 244, 0, 176, 44, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 116] := by
  decide +kernel

theorem primitive_host_0772_semantics :
    (Generated.hostChunk064[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[4]).mask = 61183 := by decide +kernel
  have hv : (Generated.hostChunk064[4]).primitive.toList = [28, 0, 0, 0, 0, 96, 276, 244, 0, 176, 44, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 116] := by decide +kernel
  rw [hm, hv, primitive_values_0772]
  rfl

theorem primitive_values_0773 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61244) = [22, 20, 20, 0, 20, 48, 60, 98, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0773_semantics :
    (Generated.hostChunk064[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[5]).mask = 61244 := by decide +kernel
  have hv : (Generated.hostChunk064[5]).primitive.toList = [22, 20, 20, 0, 20, 48, 60, 98, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0773]
  rfl

theorem primitive_values_0774 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61245) = [24, 20, 24, 8, 24, 62, 114, 132, 8, 46, 16, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0774_semantics :
    (Generated.hostChunk064[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[6]).mask = 61245 := by decide +kernel
  have hv : (Generated.hostChunk064[6]).primitive.toList = [24, 20, 24, 8, 24, 62, 114, 132, 8, 46, 16, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0774]
  rfl

theorem primitive_values_0775 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61247) = [26, 20, 28, 16, 28, 78, 192, 178, 16, 96, 40, 0, 0, 0, 0, 0, 16, 8, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0775_semantics :
    (Generated.hostChunk064[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[7]).mask = 61247 := by decide +kernel
  have hv : (Generated.hostChunk064[7]).primitive.toList = [26, 20, 28, 16, 28, 78, 192, 178, 16, 96, 40, 0, 0, 0, 0, 0, 16, 8, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0775]
  rfl

theorem primitive_values_0776 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61308) = [24, 0, 0, 0, 0, 60, 96, 128, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0776_semantics :
    (Generated.hostChunk064[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[8]).mask = 61308 := by decide +kernel
  have hv : (Generated.hostChunk064[8]).primitive.toList = [24, 0, 0, 0, 0, 60, 96, 128, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0776]
  rfl

theorem primitive_values_0777 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61309) = [26, 0, 0, 0, 0, 76, 168, 176, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 28] := by
  decide +kernel

theorem primitive_host_0777_semantics :
    (Generated.hostChunk064[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[9]).mask = 61309 := by decide +kernel
  have hv : (Generated.hostChunk064[9]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 176, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0777]
  rfl

theorem primitive_values_0778 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61311) = [28, 0, 0, 0, 0, 94, 264, 236, 0, 156, 44, 0, 0, 48, 0, 8, 0, 0, 4, 4, 0, 92] := by
  decide +kernel

theorem primitive_host_0778_semantics :
    (Generated.hostChunk064[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[10]).mask = 61311 := by decide +kernel
  have hv : (Generated.hostChunk064[10]).primitive.toList = [28, 0, 0, 0, 0, 94, 264, 236, 0, 156, 44, 0, 0, 48, 0, 8, 0, 0, 4, 4, 0, 92] := by decide +kernel
  rw [hm, hv, primitive_values_0778]
  rfl

theorem primitive_values_0779 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61372) = [24, 0, 0, 0, 0, 60, 96, 136, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0779_semantics :
    (Generated.hostChunk064[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk064[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk064[11]).mask = 61372 := by decide +kernel
  have hv : (Generated.hostChunk064[11]).primitive.toList = [24, 0, 0, 0, 0, 60, 96, 136, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0779]
  rfl

theorem primitive_chunk_064_semantics :
    ∀ h ∈ Generated.hostChunk064.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk064.toList = [Generated.hostChunk064[0], Generated.hostChunk064[1], Generated.hostChunk064[2], Generated.hostChunk064[3], Generated.hostChunk064[4], Generated.hostChunk064[5], Generated.hostChunk064[6], Generated.hostChunk064[7], Generated.hostChunk064[8], Generated.hostChunk064[9], Generated.hostChunk064[10], Generated.hostChunk064[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0768_semantics
  · exact primitive_host_0769_semantics
  · exact primitive_host_0770_semantics
  · exact primitive_host_0771_semantics
  · exact primitive_host_0772_semantics
  · exact primitive_host_0773_semantics
  · exact primitive_host_0774_semantics
  · exact primitive_host_0775_semantics
  · exact primitive_host_0776_semantics
  · exact primitive_host_0777_semantics
  · exact primitive_host_0778_semantics
  · exact primitive_host_0779_semantics

end InducedPentagons.Paper

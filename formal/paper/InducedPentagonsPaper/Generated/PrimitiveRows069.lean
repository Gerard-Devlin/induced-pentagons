import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData069
import InducedPentagonsPaper.Generated.PrimitiveRows061

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0828 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113963) = [22, 0, 0, 0, 0, 52, 84, 92, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0828_semantics :
    (Generated.hostChunk069[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[0]).mask = 113963 := by decide +kernel
  have hv : (Generated.hostChunk069[0]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 92, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0828]
  rfl

theorem primitive_values_0829 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113967) = [24, 0, 0, 0, 0, 66, 138, 136, 0, 82, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0829_semantics :
    (Generated.hostChunk069[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[1]).mask = 113967 := by decide +kernel
  have hv : (Generated.hostChunk069[1]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 136, 0, 82, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0829]
  rfl

theorem primitive_values_0830 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113969) = [20, 20, 20, 0, 0, 38, 36, 54, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0830_semantics :
    (Generated.hostChunk069[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[2]).mask = 113969 := by decide +kernel
  have hv : (Generated.hostChunk069[2]).primitive.toList = [20, 20, 20, 0, 0, 38, 36, 54, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0830]
  rfl

theorem primitive_values_0831 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113970) = [20, 10, 8, 4, 8, 40, 48, 64, 4, 24, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0831_semantics :
    (Generated.hostChunk069[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[3]).mask = 113970 := by decide +kernel
  have hv : (Generated.hostChunk069[3]).primitive.toList = [20, 10, 8, 4, 8, 40, 48, 64, 4, 24, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0831]
  rfl

theorem primitive_values_0832 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113971) = [22, 10, 12, 4, 0, 50, 72, 88, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0832_semantics :
    (Generated.hostChunk069[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[4]).mask = 113971 := by decide +kernel
  have hv : (Generated.hostChunk069[4]).primitive.toList = [22, 10, 12, 4, 0, 50, 72, 88, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0832]
  rfl

theorem primitive_values_0833 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113974) = [22, 20, 20, 16, 20, 52, 84, 96, 16, 52, 8, 0, 0, 24, 8, 0, 16, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0833_semantics :
    (Generated.hostChunk069[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[5]).mask = 113974 := by decide +kernel
  have hv : (Generated.hostChunk069[5]).primitive.toList = [22, 20, 20, 16, 20, 52, 84, 96, 16, 52, 8, 0, 0, 24, 8, 0, 16, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0833]
  rfl

theorem primitive_values_0834 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113975) = [24, 0, 0, 0, 0, 64, 126, 130, 0, 66, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0834_semantics :
    (Generated.hostChunk069[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[6]).mask = 113975 := by decide +kernel
  have hv : (Generated.hostChunk069[6]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 130, 0, 66, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0834]
  rfl

theorem primitive_values_0835 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113977) = [22, 0, 0, 0, 0, 50, 72, 88, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0835_semantics :
    (Generated.hostChunk069[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[7]).mask = 113977 := by decide +kernel
  have hv : (Generated.hostChunk069[7]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 88, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0835]
  rfl

theorem primitive_values_0836 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113978) = [22, 0, 0, 0, 0, 52, 84, 100, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0836_semantics :
    (Generated.hostChunk069[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[8]).mask = 113978 := by decide +kernel
  have hv : (Generated.hostChunk069[8]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 100, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0836]
  rfl

theorem primitive_values_0837 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113979) = [24, 0, 0, 0, 0, 64, 126, 130, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0837_semantics :
    (Generated.hostChunk069[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[9]).mask = 113979 := by decide +kernel
  have hv : (Generated.hostChunk069[9]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 130, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0837]
  rfl

theorem primitive_values_0838 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113982) = [24, 0, 0, 0, 0, 66, 138, 140, 0, 88, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0838_semantics :
    (Generated.hostChunk069[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[10]).mask = 113982 := by decide +kernel
  have hv : (Generated.hostChunk069[10]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 140, 0, 88, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0838]
  rfl

theorem primitive_values_0839 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113983) = [26, 0, 0, 0, 0, 80, 204, 180, 0, 122, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0839_semantics :
    (Generated.hostChunk069[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk069[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk069[11]).mask = 113983 := by decide +kernel
  have hv : (Generated.hostChunk069[11]).primitive.toList = [26, 0, 0, 0, 0, 80, 204, 180, 0, 122, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0839]
  rfl

theorem primitive_chunk_069_semantics :
    ∀ h ∈ Generated.hostChunk069.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk069.toList = [Generated.hostChunk069[0], Generated.hostChunk069[1], Generated.hostChunk069[2], Generated.hostChunk069[3], Generated.hostChunk069[4], Generated.hostChunk069[5], Generated.hostChunk069[6], Generated.hostChunk069[7], Generated.hostChunk069[8], Generated.hostChunk069[9], Generated.hostChunk069[10], Generated.hostChunk069[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0828_semantics
  · exact primitive_host_0829_semantics
  · exact primitive_host_0830_semantics
  · exact primitive_host_0831_semantics
  · exact primitive_host_0832_semantics
  · exact primitive_host_0833_semantics
  · exact primitive_host_0834_semantics
  · exact primitive_host_0835_semantics
  · exact primitive_host_0836_semantics
  · exact primitive_host_0837_semantics
  · exact primitive_host_0838_semantics
  · exact primitive_host_0839_semantics

end InducedPentagons.Paper

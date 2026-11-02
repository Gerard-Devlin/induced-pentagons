import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData073
import InducedPentagonsPaper.Generated.PrimitiveRows065

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0876 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114686) = [30, 0, 0, 0, 0, 106, 288, 296, 0, 196, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by
  decide +kernel

theorem primitive_host_0876_semantics :
    (Generated.hostChunk073[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[0]).mask = 114686 := by decide +kernel
  have hv : (Generated.hostChunk073[0]).primitive.toList = [30, 0, 0, 0, 0, 106, 288, 296, 0, 196, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by decide +kernel
  rw [hm, hv, primitive_values_0876]
  rfl

theorem primitive_values_0877 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114687) = [32, 0, 0, 0, 0, 126, 408, 376, 0, 316, 40, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 256] := by
  decide +kernel

theorem primitive_host_0877_semantics :
    (Generated.hostChunk073[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[1]).mask = 114687 := by decide +kernel
  have hv : (Generated.hostChunk073[1]).primitive.toList = [32, 0, 0, 0, 0, 126, 408, 376, 0, 316, 40, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 256] := by decide +kernel
  rw [hm, hv, primitive_values_0877]
  rfl

theorem primitive_values_0878 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120383) = [24, 0, 0, 0, 0, 66, 156, 132, 0, 72, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0878_semantics :
    (Generated.hostChunk073[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[2]).mask = 120383 := by decide +kernel
  have hv : (Generated.hostChunk073[2]).primitive.toList = [24, 0, 0, 0, 0, 66, 156, 132, 0, 72, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0878]
  rfl

theorem primitive_values_0879 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120443) = [24, 10, 12, 8, 12, 64, 126, 134, 8, 72, 16, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0879_semantics :
    (Generated.hostChunk073[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[3]).mask = 120443 := by decide +kernel
  have hv : (Generated.hostChunk073[3]).primitive.toList = [24, 10, 12, 8, 12, 64, 126, 134, 8, 72, 16, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0879]
  rfl

theorem primitive_values_0880 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120444) = [22, 20, 22, 4, 10, 48, 60, 86, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0880_semantics :
    (Generated.hostChunk073[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[4]).mask = 120444 := by decide +kernel
  have hv : (Generated.hostChunk073[4]).primitive.toList = [22, 20, 22, 4, 10, 48, 60, 86, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0880]
  rfl

theorem primitive_values_0881 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120445) = [24, 10, 12, 4, 12, 62, 114, 126, 4, 52, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0881_semantics :
    (Generated.hostChunk073[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[5]).mask = 120445 := by decide +kernel
  have hv : (Generated.hostChunk073[5]).primitive.toList = [24, 10, 12, 4, 12, 62, 114, 126, 4, 52, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0881]
  rfl

theorem primitive_values_0882 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120447) = [26, 10, 14, 8, 14, 78, 192, 174, 8, 106, 28, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0882_semantics :
    (Generated.hostChunk073[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[6]).mask = 120447 := by decide +kernel
  have hv : (Generated.hostChunk073[6]).primitive.toList = [26, 10, 14, 8, 14, 78, 192, 174, 8, 106, 28, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0882]
  rfl

theorem primitive_values_0883 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120568) = [22, 20, 24, 8, 0, 48, 60, 92, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0883_semantics :
    (Generated.hostChunk073[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[7]).mask = 120568 := by decide +kernel
  have hv : (Generated.hostChunk073[7]).primitive.toList = [22, 20, 24, 8, 0, 48, 60, 92, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0883]
  rfl

theorem primitive_values_0884 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120569) = [24, 0, 0, 0, 0, 62, 114, 132, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0884_semantics :
    (Generated.hostChunk073[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[8]).mask = 120569 := by decide +kernel
  have hv : (Generated.hostChunk073[8]).primitive.toList = [24, 0, 0, 0, 0, 62, 114, 132, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0884]
  rfl

theorem primitive_values_0885 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120570) = [24, 10, 14, 8, 0, 60, 96, 124, 0, 38, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0885_semantics :
    (Generated.hostChunk073[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[9]).mask = 120570 := by decide +kernel
  have hv : (Generated.hostChunk073[9]).primitive.toList = [24, 10, 14, 8, 0, 60, 96, 124, 0, 38, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0885]
  rfl

theorem primitive_values_0886 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120571) = [26, 0, 0, 0, 0, 76, 168, 174, 0, 90, 20, 0, 4, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0886_semantics :
    (Generated.hostChunk073[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[10]).mask = 120571 := by decide +kernel
  have hv : (Generated.hostChunk073[10]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 174, 0, 90, 20, 0, 4, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0886]
  rfl

theorem primitive_values_0887 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120574) = [26, 0, 0, 0, 0, 74, 150, 168, 0, 68, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0887_semantics :
    (Generated.hostChunk073[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk073[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk073[11]).mask = 120574 := by decide +kernel
  have hv : (Generated.hostChunk073[11]).primitive.toList = [26, 0, 0, 0, 0, 74, 150, 168, 0, 68, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0887]
  rfl

theorem primitive_chunk_073_semantics :
    ∀ h ∈ Generated.hostChunk073.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk073.toList = [Generated.hostChunk073[0], Generated.hostChunk073[1], Generated.hostChunk073[2], Generated.hostChunk073[3], Generated.hostChunk073[4], Generated.hostChunk073[5], Generated.hostChunk073[6], Generated.hostChunk073[7], Generated.hostChunk073[8], Generated.hostChunk073[9], Generated.hostChunk073[10], Generated.hostChunk073[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0876_semantics
  · exact primitive_host_0877_semantics
  · exact primitive_host_0878_semantics
  · exact primitive_host_0879_semantics
  · exact primitive_host_0880_semantics
  · exact primitive_host_0881_semantics
  · exact primitive_host_0882_semantics
  · exact primitive_host_0883_semantics
  · exact primitive_host_0884_semantics
  · exact primitive_host_0885_semantics
  · exact primitive_host_0886_semantics
  · exact primitive_host_0887_semantics

end InducedPentagons.Paper

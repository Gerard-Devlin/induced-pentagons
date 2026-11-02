import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData075
import InducedPentagonsPaper.Generated.PrimitiveRows067

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0900 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122623) = [30, 0, 0, 0, 0, 108, 318, 294, 0, 216, 48, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 144] := by
  decide +kernel

theorem primitive_host_0900_semantics :
    (Generated.hostChunk075[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[0]).mask = 122623 := by decide +kernel
  have hv : (Generated.hostChunk075[0]).primitive.toList = [30, 0, 0, 0, 0, 108, 318, 294, 0, 216, 48, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 144] := by decide +kernel
  rw [hm, hv, primitive_values_0900]
  rfl

theorem primitive_values_0901 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122681) = [24, 20, 24, 8, 24, 60, 96, 126, 8, 40, 12, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0901_semantics :
    (Generated.hostChunk075[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[1]).mask = 122681 := by decide +kernel
  have hv : (Generated.hostChunk075[1]).primitive.toList = [24, 20, 24, 8, 24, 60, 96, 126, 8, 40, 12, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0901]
  rfl

theorem primitive_values_0902 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122682) = [24, 10, 12, 4, 12, 60, 96, 132, 4, 32, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0902_semantics :
    (Generated.hostChunk075[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[2]).mask = 122682 := by decide +kernel
  have hv : (Generated.hostChunk075[2]).primitive.toList = [24, 10, 12, 4, 12, 60, 96, 132, 4, 32, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0902]
  rfl

theorem primitive_values_0903 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122683) = [26, 10, 14, 8, 14, 74, 150, 172, 8, 74, 28, 0, 0, 0, 0, 0, 8, 2, 1, 1, 0, 28] := by
  decide +kernel

theorem primitive_host_0903_semantics :
    (Generated.hostChunk075[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[3]).mask = 122683 := by decide +kernel
  have hv : (Generated.hostChunk075[3]).primitive.toList = [26, 10, 14, 8, 14, 74, 150, 172, 8, 74, 28, 0, 0, 0, 0, 0, 8, 2, 1, 1, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0903]
  rfl

theorem primitive_values_0904 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122686) = [26, 10, 14, 8, 14, 74, 150, 174, 8, 78, 16, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0904_semantics :
    (Generated.hostChunk075[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[4]).mask = 122686 := by decide +kernel
  have hv : (Generated.hostChunk075[4]).primitive.toList = [26, 10, 14, 8, 14, 74, 150, 174, 8, 78, 16, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0904]
  rfl

theorem primitive_values_0905 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122687) = [28, 10, 16, 12, 16, 90, 228, 226, 12, 132, 44, 0, 0, 24, 4, 0, 12, 2, 0, 0, 2, 68] := by
  decide +kernel

theorem primitive_host_0905_semantics :
    (Generated.hostChunk075[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[5]).mask = 122687 := by decide +kernel
  have hv : (Generated.hostChunk075[5]).primitive.toList = [28, 10, 16, 12, 16, 90, 228, 226, 12, 132, 44, 0, 0, 24, 4, 0, 12, 2, 0, 0, 2, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0905]
  rfl

theorem primitive_values_0906 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122746) = [26, 0, 0, 0, 0, 74, 150, 178, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0906_semantics :
    (Generated.hostChunk075[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[6]).mask = 122746 := by decide +kernel
  have hv : (Generated.hostChunk075[6]).primitive.toList = [26, 0, 0, 0, 0, 74, 150, 178, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0906]
  rfl

theorem primitive_values_0907 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122747) = [28, 0, 0, 0, 0, 90, 222, 230, 0, 134, 32, 0, 0, 48, 0, 8, 0, 0, 2, 2, 0, 80] := by
  decide +kernel

theorem primitive_host_0907_semantics :
    (Generated.hostChunk075[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[7]).mask = 122747 := by decide +kernel
  have hv : (Generated.hostChunk075[7]).primitive.toList = [28, 0, 0, 0, 0, 90, 222, 230, 0, 134, 32, 0, 0, 48, 0, 8, 0, 0, 2, 2, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0907]
  rfl

theorem primitive_values_0908 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122748) = [26, 0, 0, 0, 0, 72, 132, 168, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0908_semantics :
    (Generated.hostChunk075[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[8]).mask = 122748 := by decide +kernel
  have hv : (Generated.hostChunk075[8]).primitive.toList = [26, 0, 0, 0, 0, 72, 132, 168, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0908]
  rfl

theorem primitive_values_0909 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122749) = [28, 0, 0, 0, 0, 88, 204, 222, 0, 108, 44, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 44] := by
  decide +kernel

theorem primitive_host_0909_semantics :
    (Generated.hostChunk075[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[9]).mask = 122749 := by decide +kernel
  have hv : (Generated.hostChunk075[9]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 222, 0, 108, 44, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0909]
  rfl

theorem primitive_values_0910 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122750) = [28, 0, 0, 0, 0, 88, 204, 224, 0, 112, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by
  decide +kernel

theorem primitive_host_0910_semantics :
    (Generated.hostChunk075[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[10]).mask = 122750 := by decide +kernel
  have hv : (Generated.hostChunk075[10]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 224, 0, 112, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0910]
  rfl

theorem primitive_values_0911 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122751) = [30, 0, 0, 0, 0, 106, 300, 290, 0, 196, 52, 0, 0, 72, 0, 4, 0, 0, 1, 1, 2, 124] := by
  decide +kernel

theorem primitive_host_0911_semantics :
    (Generated.hostChunk075[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk075[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk075[11]).mask = 122751 := by decide +kernel
  have hv : (Generated.hostChunk075[11]).primitive.toList = [30, 0, 0, 0, 0, 106, 300, 290, 0, 196, 52, 0, 0, 72, 0, 4, 0, 0, 1, 1, 2, 124] := by decide +kernel
  rw [hm, hv, primitive_values_0911]
  rfl

theorem primitive_chunk_075_semantics :
    ∀ h ∈ Generated.hostChunk075.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk075.toList = [Generated.hostChunk075[0], Generated.hostChunk075[1], Generated.hostChunk075[2], Generated.hostChunk075[3], Generated.hostChunk075[4], Generated.hostChunk075[5], Generated.hostChunk075[6], Generated.hostChunk075[7], Generated.hostChunk075[8], Generated.hostChunk075[9], Generated.hostChunk075[10], Generated.hostChunk075[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0900_semantics
  · exact primitive_host_0901_semantics
  · exact primitive_host_0902_semantics
  · exact primitive_host_0903_semantics
  · exact primitive_host_0904_semantics
  · exact primitive_host_0905_semantics
  · exact primitive_host_0906_semantics
  · exact primitive_host_0907_semantics
  · exact primitive_host_0908_semantics
  · exact primitive_host_0909_semantics
  · exact primitive_host_0910_semantics
  · exact primitive_host_0911_semantics

end InducedPentagons.Paper

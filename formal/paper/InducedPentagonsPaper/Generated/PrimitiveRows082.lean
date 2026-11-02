import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData082
import InducedPentagonsPaper.Generated.PrimitiveRows074

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0984 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380275) = [24, 0, 0, 0, 0, 60, 96, 120, 0, 48, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0984_semantics :
    (Generated.hostChunk082[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[0]).mask = 380275 := by decide +kernel
  have hv : (Generated.hostChunk082[0]).primitive.toList = [24, 0, 0, 0, 0, 60, 96, 120, 0, 48, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0984]
  rfl

theorem primitive_values_0985 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380278) = [24, 30, 40, 20, 12, 60, 96, 120, 4, 48, 16, 8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0985_semantics :
    (Generated.hostChunk082[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[1]).mask = 380278 := by decide +kernel
  have hv : (Generated.hostChunk082[1]).primitive.toList = [24, 30, 40, 20, 12, 60, 96, 120, 4, 48, 16, 8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0985]
  rfl

theorem primitive_values_0986 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380279) = [26, 0, 0, 0, 0, 74, 150, 166, 0, 82, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0986_semantics :
    (Generated.hostChunk082[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[2]).mask = 380279 := by decide +kernel
  have hv : (Generated.hostChunk082[2]).primitive.toList = [26, 0, 0, 0, 0, 74, 150, 166, 0, 82, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0986]
  rfl

theorem primitive_values_0987 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380287) = [28, 0, 0, 0, 0, 90, 228, 220, 0, 140, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0987_semantics :
    (Generated.hostChunk082[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[3]).mask = 380287 := by decide +kernel
  have hv : (Generated.hostChunk082[3]).primitive.toList = [28, 0, 0, 0, 0, 90, 228, 220, 0, 140, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0987]
  rfl

theorem primitive_values_0988 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380406) = [26, 20, 30, 20, 14, 74, 150, 166, 8, 82, 32, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0988_semantics :
    (Generated.hostChunk082[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[4]).mask = 380406 := by decide +kernel
  have hv : (Generated.hostChunk082[4]).primitive.toList = [26, 20, 30, 20, 14, 74, 150, 166, 8, 82, 32, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0988]
  rfl

theorem primitive_values_0989 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380407) = [28, 0, 0, 0, 0, 90, 222, 224, 0, 142, 36, 0, 4, 48, 0, 4, 0, 0, 0, 0, 0, 84] := by
  decide +kernel

theorem primitive_host_0989_semantics :
    (Generated.hostChunk082[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[5]).mask = 380407 := by decide +kernel
  have hv : (Generated.hostChunk082[5]).primitive.toList = [28, 0, 0, 0, 0, 90, 222, 224, 0, 142, 36, 0, 4, 48, 0, 4, 0, 0, 0, 0, 0, 84] := by decide +kernel
  rw [hm, hv, primitive_values_0989]
  rfl

theorem primitive_values_0990 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380410) = [26, 10, 16, 12, 0, 72, 132, 162, 0, 64, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0990_semantics :
    (Generated.hostChunk082[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[6]).mask = 380410 := by decide +kernel
  have hv : (Generated.hostChunk082[6]).primitive.toList = [26, 10, 16, 12, 0, 72, 132, 162, 0, 64, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0990]
  rfl

theorem primitive_values_0991 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380411) = [28, 0, 0, 0, 0, 88, 204, 218, 0, 120, 36, 0, 4, 24, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0991_semantics :
    (Generated.hostChunk082[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[7]).mask = 380411 := by decide +kernel
  have hv : (Generated.hostChunk082[7]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 218, 0, 120, 36, 0, 4, 24, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0991]
  rfl

theorem primitive_values_0992 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380415) = [30, 0, 0, 0, 0, 106, 300, 286, 0, 208, 44, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 140] := by
  decide +kernel

theorem primitive_host_0992_semantics :
    (Generated.hostChunk082[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[8]).mask = 380415 := by decide +kernel
  have hv : (Generated.hostChunk082[8]).primitive.toList = [30, 0, 0, 0, 0, 106, 300, 286, 0, 208, 44, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 140] := by decide +kernel
  rw [hm, hv, primitive_values_0992]
  rfl

theorem primitive_values_0993 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380731) = [26, 20, 28, 16, 28, 74, 150, 168, 16, 86, 20, 0, 0, 24, 8, 0, 16, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0993_semantics :
    (Generated.hostChunk082[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[9]).mask = 380731 := by decide +kernel
  have hv : (Generated.hostChunk082[9]).primitive.toList = [26, 20, 28, 16, 28, 74, 150, 168, 16, 86, 20, 0, 0, 24, 8, 0, 16, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0993]
  rfl

theorem primitive_values_0994 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380735) = [28, 20, 32, 24, 32, 90, 228, 222, 24, 144, 36, 0, 0, 48, 16, 0, 24, 0, 0, 0, 0, 84] := by
  decide +kernel

theorem primitive_host_0994_semantics :
    (Generated.hostChunk082[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[10]).mask = 380735 := by decide +kernel
  have hv : (Generated.hostChunk082[10]).primitive.toList = [28, 20, 32, 24, 32, 90, 228, 222, 24, 144, 36, 0, 0, 48, 16, 0, 24, 0, 0, 0, 0, 84] := by decide +kernel
  rw [hm, hv, primitive_values_0994]
  rfl

theorem primitive_values_0995 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380795) = [28, 0, 0, 0, 0, 88, 204, 220, 0, 124, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0995_semantics :
    (Generated.hostChunk082[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk082[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk082[11]).mask = 380795 := by decide +kernel
  have hv : (Generated.hostChunk082[11]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 220, 0, 124, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0995]
  rfl

theorem primitive_chunk_082_semantics :
    ∀ h ∈ Generated.hostChunk082.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk082.toList = [Generated.hostChunk082[0], Generated.hostChunk082[1], Generated.hostChunk082[2], Generated.hostChunk082[3], Generated.hostChunk082[4], Generated.hostChunk082[5], Generated.hostChunk082[6], Generated.hostChunk082[7], Generated.hostChunk082[8], Generated.hostChunk082[9], Generated.hostChunk082[10], Generated.hostChunk082[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0984_semantics
  · exact primitive_host_0985_semantics
  · exact primitive_host_0986_semantics
  · exact primitive_host_0987_semantics
  · exact primitive_host_0988_semantics
  · exact primitive_host_0989_semantics
  · exact primitive_host_0990_semantics
  · exact primitive_host_0991_semantics
  · exact primitive_host_0992_semantics
  · exact primitive_host_0993_semantics
  · exact primitive_host_0994_semantics
  · exact primitive_host_0995_semantics

end InducedPentagons.Paper

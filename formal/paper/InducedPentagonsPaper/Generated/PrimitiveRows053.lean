import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData053
import InducedPentagonsPaper.Generated.PrimitiveRows045

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0636 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 45055) = [28, 0, 0, 0, 0, 98, 300, 246, 0, 180, 44, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 116] := by
  decide +kernel

theorem primitive_host_0636_semantics :
    (Generated.hostChunk053[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[0]).mask = 45055 := by decide +kernel
  have hv : (Generated.hostChunk053[0]).primitive.toList = [28, 0, 0, 0, 0, 98, 300, 246, 0, 180, 44, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 116] := by decide +kernel
  rw [hm, hv, primitive_values_0636]
  rfl

theorem primitive_values_0637 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48029) = [22, 0, 0, 0, 0, 60, 108, 128, 0, 68, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0637_semantics :
    (Generated.hostChunk053[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[1]).mask = 48029 := by decide +kernel
  have hv : (Generated.hostChunk053[1]).primitive.toList = [22, 0, 0, 0, 0, 60, 108, 128, 0, 68, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0637]
  rfl

theorem primitive_values_0638 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48031) = [24, 0, 0, 0, 0, 74, 162, 172, 0, 118, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0638_semantics :
    (Generated.hostChunk053[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[2]).mask = 48031 := by decide +kernel
  have hv : (Generated.hostChunk053[2]).primitive.toList = [24, 0, 0, 0, 0, 74, 162, 172, 0, 118, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0638]
  rfl

theorem primitive_values_0639 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48044) = [20, 0, 0, 0, 0, 44, 66, 80, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0639_semantics :
    (Generated.hostChunk053[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[3]).mask = 48044 := by decide +kernel
  have hv : (Generated.hostChunk053[3]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 80, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0639]
  rfl

theorem primitive_values_0640 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48045) = [22, 0, 0, 0, 0, 56, 102, 112, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0640_semantics :
    (Generated.hostChunk053[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[4]).mask = 48045 := by decide +kernel
  have hv : (Generated.hostChunk053[4]).primitive.toList = [22, 0, 0, 0, 0, 56, 102, 112, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0640]
  rfl

theorem primitive_values_0641 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48047) = [24, 0, 0, 0, 0, 70, 156, 156, 0, 94, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0641_semantics :
    (Generated.hostChunk053[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[5]).mask = 48047 := by decide +kernel
  have hv : (Generated.hostChunk053[5]).primitive.toList = [24, 0, 0, 0, 0, 70, 156, 156, 0, 94, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0641]
  rfl

theorem primitive_values_0642 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48048) = [18, 0, 0, 0, 0, 32, 30, 48, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0642_semantics :
    (Generated.hostChunk053[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[6]).mask = 48048 := by decide +kernel
  have hv : (Generated.hostChunk053[6]).primitive.toList = [18, 0, 0, 0, 0, 32, 30, 48, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0642]
  rfl

theorem primitive_values_0643 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48049) = [20, 0, 0, 0, 0, 42, 54, 70, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0643_semantics :
    (Generated.hostChunk053[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[7]).mask = 48049 := by decide +kernel
  have hv : (Generated.hostChunk053[7]).primitive.toList = [20, 0, 0, 0, 0, 42, 54, 70, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0643]
  rfl

theorem primitive_values_0644 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48051) = [22, 0, 0, 0, 0, 54, 90, 104, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0644_semantics :
    (Generated.hostChunk053[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[8]).mask = 48051 := by decide +kernel
  have hv : (Generated.hostChunk053[8]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 104, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0644]
  rfl

theorem primitive_values_0645 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48052) = [20, 0, 0, 0, 0, 42, 54, 76, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0645_semantics :
    (Generated.hostChunk053[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[9]).mask = 48052 := by decide +kernel
  have hv : (Generated.hostChunk053[9]).primitive.toList = [20, 0, 0, 0, 0, 42, 54, 76, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0645]
  rfl

theorem primitive_values_0646 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48053) = [22, 0, 0, 0, 0, 54, 90, 106, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0646_semantics :
    (Generated.hostChunk053[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[10]).mask = 48053 := by decide +kernel
  have hv : (Generated.hostChunk053[10]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 106, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0646]
  rfl

theorem primitive_values_0647 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48055) = [24, 0, 0, 0, 0, 68, 144, 148, 0, 72, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0647_semantics :
    (Generated.hostChunk053[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk053[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk053[11]).mask = 48055 := by decide +kernel
  have hv : (Generated.hostChunk053[11]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 148, 0, 72, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0647]
  rfl

theorem primitive_chunk_053_semantics :
    ∀ h ∈ Generated.hostChunk053.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk053.toList = [Generated.hostChunk053[0], Generated.hostChunk053[1], Generated.hostChunk053[2], Generated.hostChunk053[3], Generated.hostChunk053[4], Generated.hostChunk053[5], Generated.hostChunk053[6], Generated.hostChunk053[7], Generated.hostChunk053[8], Generated.hostChunk053[9], Generated.hostChunk053[10], Generated.hostChunk053[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0636_semantics
  · exact primitive_host_0637_semantics
  · exact primitive_host_0638_semantics
  · exact primitive_host_0639_semantics
  · exact primitive_host_0640_semantics
  · exact primitive_host_0641_semantics
  · exact primitive_host_0642_semantics
  · exact primitive_host_0643_semantics
  · exact primitive_host_0644_semantics
  · exact primitive_host_0645_semantics
  · exact primitive_host_0646_semantics
  · exact primitive_host_0647_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData054
import InducedPentagonsPaper.Generated.PrimitiveRows046

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0648 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48060) = [22, 0, 0, 0, 0, 54, 90, 112, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0648_semantics :
    (Generated.hostChunk054[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[0]).mask = 48060 := by decide +kernel
  have hv : (Generated.hostChunk054[0]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 112, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0648]
  rfl

theorem primitive_values_0649 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48061) = [24, 0, 0, 0, 0, 68, 144, 150, 0, 76, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0649_semantics :
    (Generated.hostChunk054[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[1]).mask = 48061 := by decide +kernel
  have hv : (Generated.hostChunk054[1]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 150, 0, 76, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0649]
  rfl

theorem primitive_values_0650 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48063) = [26, 0, 0, 0, 0, 84, 222, 200, 0, 132, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0650_semantics :
    (Generated.hostChunk054[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[2]).mask = 48063 := by decide +kernel
  have hv : (Generated.hostChunk054[2]).primitive.toList = [26, 0, 0, 0, 0, 84, 222, 200, 0, 132, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0650]
  rfl

theorem primitive_values_0651 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48095) = [26, 0, 0, 0, 0, 90, 234, 228, 0, 198, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0651_semantics :
    (Generated.hostChunk054[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[3]).mask = 48095 := by decide +kernel
  have hv : (Generated.hostChunk054[3]).primitive.toList = [26, 0, 0, 0, 0, 90, 234, 228, 0, 198, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0651]
  rfl

theorem primitive_values_0652 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48108) = [22, 0, 0, 0, 0, 56, 102, 108, 0, 66, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0652_semantics :
    (Generated.hostChunk054[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[4]).mask = 48108 := by decide +kernel
  have hv : (Generated.hostChunk054[4]).primitive.toList = [22, 0, 0, 0, 0, 56, 102, 108, 0, 66, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0652]
  rfl

theorem primitive_values_0653 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48109) = [24, 0, 0, 0, 0, 70, 156, 152, 0, 104, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0653_semantics :
    (Generated.hostChunk054[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[5]).mask = 48109 := by decide +kernel
  have hv : (Generated.hostChunk054[5]).primitive.toList = [24, 0, 0, 0, 0, 70, 156, 152, 0, 104, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0653]
  rfl

theorem primitive_values_0654 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48111) = [26, 0, 0, 0, 0, 86, 228, 208, 0, 168, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by
  decide +kernel

theorem primitive_host_0654_semantics :
    (Generated.hostChunk054[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[6]).mask = 48111 := by decide +kernel
  have hv : (Generated.hostChunk054[6]).primitive.toList = [26, 0, 0, 0, 0, 86, 228, 208, 0, 168, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by decide +kernel
  rw [hm, hv, primitive_values_0654]
  rfl

theorem primitive_values_0655 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48112) = [20, 0, 0, 0, 0, 44, 66, 72, 0, 46, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0655_semantics :
    (Generated.hostChunk054[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[7]).mask = 48112 := by decide +kernel
  have hv : (Generated.hostChunk054[7]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 72, 0, 46, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0655]
  rfl

theorem primitive_values_0656 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48113) = [22, 0, 0, 0, 0, 56, 108, 104, 0, 64, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0656_semantics :
    (Generated.hostChunk054[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[8]).mask = 48113 := by decide +kernel
  have hv : (Generated.hostChunk054[8]).primitive.toList = [22, 0, 0, 0, 0, 56, 108, 104, 0, 64, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0656]
  rfl

theorem primitive_values_0657 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48115) = [24, 0, 0, 0, 0, 70, 162, 148, 0, 102, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0657_semantics :
    (Generated.hostChunk054[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[9]).mask = 48115 := by decide +kernel
  have hv : (Generated.hostChunk054[9]).primitive.toList = [24, 0, 0, 0, 0, 70, 162, 148, 0, 102, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0657]
  rfl

theorem primitive_values_0658 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48116) = [22, 0, 0, 0, 0, 54, 90, 104, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0658_semantics :
    (Generated.hostChunk054[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[10]).mask = 48116 := by decide +kernel
  have hv : (Generated.hostChunk054[10]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 104, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0658]
  rfl

theorem primitive_values_0659 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48117) = [24, 0, 0, 0, 0, 68, 144, 146, 0, 86, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0659_semantics :
    (Generated.hostChunk054[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk054[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk054[11]).mask = 48117 := by decide +kernel
  have hv : (Generated.hostChunk054[11]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 146, 0, 86, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0659]
  rfl

theorem primitive_chunk_054_semantics :
    ∀ h ∈ Generated.hostChunk054.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk054.toList = [Generated.hostChunk054[0], Generated.hostChunk054[1], Generated.hostChunk054[2], Generated.hostChunk054[3], Generated.hostChunk054[4], Generated.hostChunk054[5], Generated.hostChunk054[6], Generated.hostChunk054[7], Generated.hostChunk054[8], Generated.hostChunk054[9], Generated.hostChunk054[10], Generated.hostChunk054[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0648_semantics
  · exact primitive_host_0649_semantics
  · exact primitive_host_0650_semantics
  · exact primitive_host_0651_semantics
  · exact primitive_host_0652_semantics
  · exact primitive_host_0653_semantics
  · exact primitive_host_0654_semantics
  · exact primitive_host_0655_semantics
  · exact primitive_host_0656_semantics
  · exact primitive_host_0657_semantics
  · exact primitive_host_0658_semantics
  · exact primitive_host_0659_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData012
import InducedPentagonsPaper.Generated.PrimitiveRows004

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0144 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2879) = [18, 0, 0, 0, 0, 44, 126, 52, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0144_semantics :
    (Generated.hostChunk012[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[0]).mask = 2879 := by decide +kernel
  have hv : (Generated.hostChunk012[0]).primitive.toList = [18, 0, 0, 0, 0, 44, 126, 52, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0144]
  rfl

theorem primitive_values_0145 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2906) = [14, 0, 0, 0, 0, 22, 18, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0145_semantics :
    (Generated.hostChunk012[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[1]).mask = 2906 := by decide +kernel
  have hv : (Generated.hostChunk012[1]).primitive.toList = [14, 0, 0, 0, 0, 22, 18, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0145]
  rfl

theorem primitive_values_0146 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2907) = [16, 0, 0, 0, 0, 34, 54, 48, 0, 26, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0146_semantics :
    (Generated.hostChunk012[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[2]).mask = 2907 := by decide +kernel
  have hv : (Generated.hostChunk012[2]).primitive.toList = [16, 0, 0, 0, 0, 34, 54, 48, 0, 26, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0146]
  rfl

theorem primitive_values_0147 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2908) = [14, 20, 8, 0, 0, 20, 12, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0147_semantics :
    (Generated.hostChunk012[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[3]).mask = 2908 := by decide +kernel
  have hv : (Generated.hostChunk012[3]).primitive.toList = [14, 20, 8, 0, 0, 20, 12, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0147]
  rfl

theorem primitive_values_0148 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2909) = [16, 0, 0, 0, 0, 32, 48, 44, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0148_semantics :
    (Generated.hostChunk012[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[4]).mask = 2909 := by decide +kernel
  have hv : (Generated.hostChunk012[4]).primitive.toList = [16, 0, 0, 0, 0, 32, 48, 44, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0148]
  rfl

theorem primitive_values_0149 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2910) = [16, 0, 0, 0, 0, 30, 36, 44, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0149_semantics :
    (Generated.hostChunk012[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[5]).mask = 2910 := by decide +kernel
  have hv : (Generated.hostChunk012[5]).primitive.toList = [16, 0, 0, 0, 0, 30, 36, 44, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0149]
  rfl

theorem primitive_values_0150 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2911) = [18, 0, 0, 0, 0, 44, 90, 68, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0150_semantics :
    (Generated.hostChunk012[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[6]).mask = 2911 := by decide +kernel
  have hv : (Generated.hostChunk012[6]).primitive.toList = [18, 0, 0, 0, 0, 44, 90, 68, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0150]
  rfl

theorem primitive_values_0151 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2922) = [14, 0, 0, 0, 0, 20, 18, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0151_semantics :
    (Generated.hostChunk012[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[7]).mask = 2922 := by decide +kernel
  have hv : (Generated.hostChunk012[7]).primitive.toList = [14, 0, 0, 0, 0, 20, 18, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0151]
  rfl

theorem primitive_values_0152 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2923) = [16, 0, 0, 0, 0, 32, 54, 42, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0152_semantics :
    (Generated.hostChunk012[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[8]).mask = 2923 := by decide +kernel
  have hv : (Generated.hostChunk012[8]).primitive.toList = [16, 0, 0, 0, 0, 32, 54, 42, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0152]
  rfl

theorem primitive_values_0153 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2924) = [14, 10, 4, 0, 0, 18, 12, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0153_semantics :
    (Generated.hostChunk012[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[9]).mask = 2924 := by decide +kernel
  have hv : (Generated.hostChunk012[9]).primitive.toList = [14, 10, 4, 0, 0, 18, 12, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0153]
  rfl

theorem primitive_values_0154 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2925) = [16, 0, 0, 0, 0, 30, 48, 38, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0154_semantics :
    (Generated.hostChunk012[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[10]).mask = 2925 := by decide +kernel
  have hv : (Generated.hostChunk012[10]).primitive.toList = [16, 0, 0, 0, 0, 30, 48, 38, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0154]
  rfl

theorem primitive_values_0155 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2926) = [16, 0, 0, 0, 0, 28, 36, 34, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0155_semantics :
    (Generated.hostChunk012[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk012[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk012[11]).mask = 2926 := by decide +kernel
  have hv : (Generated.hostChunk012[11]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 34, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0155]
  rfl

theorem primitive_chunk_012_semantics :
    ∀ h ∈ Generated.hostChunk012.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk012.toList = [Generated.hostChunk012[0], Generated.hostChunk012[1], Generated.hostChunk012[2], Generated.hostChunk012[3], Generated.hostChunk012[4], Generated.hostChunk012[5], Generated.hostChunk012[6], Generated.hostChunk012[7], Generated.hostChunk012[8], Generated.hostChunk012[9], Generated.hostChunk012[10], Generated.hostChunk012[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0144_semantics
  · exact primitive_host_0145_semantics
  · exact primitive_host_0146_semantics
  · exact primitive_host_0147_semantics
  · exact primitive_host_0148_semantics
  · exact primitive_host_0149_semantics
  · exact primitive_host_0150_semantics
  · exact primitive_host_0151_semantics
  · exact primitive_host_0152_semantics
  · exact primitive_host_0153_semantics
  · exact primitive_host_0154_semantics
  · exact primitive_host_0155_semantics

end InducedPentagons.Paper

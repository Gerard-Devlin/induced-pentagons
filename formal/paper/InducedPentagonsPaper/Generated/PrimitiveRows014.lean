import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData014
import InducedPentagonsPaper.Generated.PrimitiveRows006

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0168 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3055) = [20, 0, 0, 0, 0, 54, 132, 90, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0168_semantics :
    (Generated.hostChunk014[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[0]).mask = 3055 := by decide +kernel
  have hv : (Generated.hostChunk014[0]).primitive.toList = [20, 0, 0, 0, 0, 54, 132, 90, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0168]
  rfl

theorem primitive_values_0169 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3064) = [16, 0, 0, 0, 0, 26, 30, 28, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0169_semantics :
    (Generated.hostChunk014[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[1]).mask = 3064 := by decide +kernel
  have hv : (Generated.hostChunk014[1]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 28, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0169]
  rfl

theorem primitive_values_0170 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3065) = [18, 0, 0, 0, 0, 40, 84, 52, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0170_semantics :
    (Generated.hostChunk014[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[2]).mask = 3065 := by decide +kernel
  have hv : (Generated.hostChunk014[2]).primitive.toList = [18, 0, 0, 0, 0, 40, 84, 52, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0170]
  rfl

theorem primitive_values_0171 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3066) = [18, 0, 0, 0, 0, 36, 54, 52, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0171_semantics :
    (Generated.hostChunk014[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[3]).mask = 3066 := by decide +kernel
  have hv : (Generated.hostChunk014[3]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 52, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0171]
  rfl

theorem primitive_values_0172 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3067) = [20, 0, 0, 0, 0, 52, 126, 84, 0, 46, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0172_semantics :
    (Generated.hostChunk014[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[4]).mask = 3067 := by decide +kernel
  have hv : (Generated.hostChunk014[4]).primitive.toList = [20, 0, 0, 0, 0, 52, 126, 84, 0, 46, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0172]
  rfl

theorem primitive_values_0173 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3070) = [20, 0, 0, 0, 0, 48, 96, 80, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0173_semantics :
    (Generated.hostChunk014[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[5]).mask = 3070 := by decide +kernel
  have hv : (Generated.hostChunk014[5]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 80, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0173]
  rfl

theorem primitive_values_0174 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3071) = [22, 0, 0, 0, 0, 66, 192, 120, 0, 82, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0174_semantics :
    (Generated.hostChunk014[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[6]).mask = 3071 := by decide +kernel
  have hv : (Generated.hostChunk014[6]).primitive.toList = [22, 0, 0, 0, 0, 66, 192, 120, 0, 82, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0174]
  rfl

theorem primitive_values_0175 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3896) = [14, 0, 0, 0, 0, 18, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0175_semantics :
    (Generated.hostChunk014[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[7]).mask = 3896 := by decide +kernel
  have hv : (Generated.hostChunk014[7]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0175]
  rfl

theorem primitive_values_0176 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3897) = [16, 0, 0, 0, 0, 30, 48, 36, 0, 24, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0176_semantics :
    (Generated.hostChunk014[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[8]).mask = 3897 := by decide +kernel
  have hv : (Generated.hostChunk014[8]).primitive.toList = [16, 0, 0, 0, 0, 30, 48, 36, 0, 24, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0176]
  rfl

theorem primitive_values_0177 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3898) = [16, 0, 0, 0, 0, 26, 30, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0177_semantics :
    (Generated.hostChunk014[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[9]).mask = 3898 := by decide +kernel
  have hv : (Generated.hostChunk014[9]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0177]
  rfl

theorem primitive_values_0178 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3899) = [18, 0, 0, 0, 0, 40, 84, 56, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0178_semantics :
    (Generated.hostChunk014[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[10]).mask = 3899 := by decide +kernel
  have hv : (Generated.hostChunk014[10]).primitive.toList = [18, 0, 0, 0, 0, 40, 84, 56, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0178]
  rfl

theorem primitive_values_0179 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3902) = [18, 0, 0, 0, 0, 36, 66, 48, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0179_semantics :
    (Generated.hostChunk014[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk014[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk014[11]).mask = 3902 := by decide +kernel
  have hv : (Generated.hostChunk014[11]).primitive.toList = [18, 0, 0, 0, 0, 36, 66, 48, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0179]
  rfl

theorem primitive_chunk_014_semantics :
    ∀ h ∈ Generated.hostChunk014.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk014.toList = [Generated.hostChunk014[0], Generated.hostChunk014[1], Generated.hostChunk014[2], Generated.hostChunk014[3], Generated.hostChunk014[4], Generated.hostChunk014[5], Generated.hostChunk014[6], Generated.hostChunk014[7], Generated.hostChunk014[8], Generated.hostChunk014[9], Generated.hostChunk014[10], Generated.hostChunk014[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0168_semantics
  · exact primitive_host_0169_semantics
  · exact primitive_host_0170_semantics
  · exact primitive_host_0171_semantics
  · exact primitive_host_0172_semantics
  · exact primitive_host_0173_semantics
  · exact primitive_host_0174_semantics
  · exact primitive_host_0175_semantics
  · exact primitive_host_0176_semantics
  · exact primitive_host_0177_semantics
  · exact primitive_host_0178_semantics
  · exact primitive_host_0179_semantics

end InducedPentagons.Paper

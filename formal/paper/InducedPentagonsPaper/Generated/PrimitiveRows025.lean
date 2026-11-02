import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData025
import InducedPentagonsPaper.Generated.PrimitiveRows017

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0300 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7863) = [20, 0, 0, 0, 0, 48, 96, 80, 0, 42, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0300_semantics :
    (Generated.hostChunk025[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[0]).mask = 7863 := by decide +kernel
  have hv : (Generated.hostChunk025[0]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 80, 0, 42, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0300]
  rfl

theorem primitive_values_0301 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7864) = [16, 0, 0, 0, 0, 22, 12, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0301_semantics :
    (Generated.hostChunk025[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[1]).mask = 7864 := by decide +kernel
  have hv : (Generated.hostChunk025[1]).primitive.toList = [16, 0, 0, 0, 0, 22, 12, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0301]
  rfl

theorem primitive_values_0302 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7865) = [18, 10, 8, 8, 0, 34, 48, 46, 0, 16, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0302_semantics :
    (Generated.hostChunk025[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[2]).mask = 7865 := by decide +kernel
  have hv : (Generated.hostChunk025[2]).primitive.toList = [18, 10, 8, 8, 0, 34, 48, 46, 0, 16, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0302]
  rfl

theorem primitive_values_0303 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7866) = [18, 20, 16, 8, 0, 32, 36, 44, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0303_semantics :
    (Generated.hostChunk025[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[3]).mask = 7866 := by decide +kernel
  have hv : (Generated.hostChunk025[3]).primitive.toList = [18, 20, 16, 8, 0, 32, 36, 44, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0303]
  rfl

theorem primitive_values_0304 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7867) = [20, 0, 0, 0, 0, 46, 90, 72, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0304_semantics :
    (Generated.hostChunk025[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[4]).mask = 7867 := by decide +kernel
  have hv : (Generated.hostChunk025[4]).primitive.toList = [20, 0, 0, 0, 0, 46, 90, 72, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0304]
  rfl

theorem primitive_values_0305 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7868) = [18, 0, 0, 0, 0, 32, 36, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0305_semantics :
    (Generated.hostChunk025[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[5]).mask = 7868 := by decide +kernel
  have hv : (Generated.hostChunk025[5]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0305]
  rfl

theorem primitive_values_0306 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7869) = [20, 0, 0, 0, 0, 46, 90, 76, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0306_semantics :
    (Generated.hostChunk025[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[6]).mask = 7869 := by decide +kernel
  have hv : (Generated.hostChunk025[6]).primitive.toList = [20, 0, 0, 0, 0, 46, 90, 76, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0306]
  rfl

theorem primitive_values_0307 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7870) = [20, 0, 0, 0, 0, 44, 78, 72, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0307_semantics :
    (Generated.hostChunk025[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[7]).mask = 7870 := by decide +kernel
  have hv : (Generated.hostChunk025[7]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 72, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0307]
  rfl

theorem primitive_values_0308 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7871) = [22, 0, 0, 0, 0, 60, 156, 106, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0308_semantics :
    (Generated.hostChunk025[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[8]).mask = 7871 := by decide +kernel
  have hv : (Generated.hostChunk025[8]).primitive.toList = [22, 0, 0, 0, 0, 60, 156, 106, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0308]
  rfl

theorem primitive_values_0309 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7926) = [20, 0, 0, 0, 0, 46, 78, 84, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0309_semantics :
    (Generated.hostChunk025[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[9]).mask = 7926 := by decide +kernel
  have hv : (Generated.hostChunk025[9]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 84, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0309]
  rfl

theorem primitive_values_0310 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7927) = [22, 0, 0, 0, 0, 62, 150, 120, 0, 78, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0310_semantics :
    (Generated.hostChunk025[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[10]).mask = 7927 := by decide +kernel
  have hv : (Generated.hostChunk025[10]).primitive.toList = [22, 0, 0, 0, 0, 62, 150, 120, 0, 78, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0310]
  rfl

theorem primitive_values_0311 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7930) = [20, 0, 0, 0, 0, 44, 72, 72, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0311_semantics :
    (Generated.hostChunk025[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk025[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk025[11]).mask = 7930 := by decide +kernel
  have hv : (Generated.hostChunk025[11]).primitive.toList = [20, 0, 0, 0, 0, 44, 72, 72, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0311]
  rfl

theorem primitive_chunk_025_semantics :
    ∀ h ∈ Generated.hostChunk025.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk025.toList = [Generated.hostChunk025[0], Generated.hostChunk025[1], Generated.hostChunk025[2], Generated.hostChunk025[3], Generated.hostChunk025[4], Generated.hostChunk025[5], Generated.hostChunk025[6], Generated.hostChunk025[7], Generated.hostChunk025[8], Generated.hostChunk025[9], Generated.hostChunk025[10], Generated.hostChunk025[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0300_semantics
  · exact primitive_host_0301_semantics
  · exact primitive_host_0302_semantics
  · exact primitive_host_0303_semantics
  · exact primitive_host_0304_semantics
  · exact primitive_host_0305_semantics
  · exact primitive_host_0306_semantics
  · exact primitive_host_0307_semantics
  · exact primitive_host_0308_semantics
  · exact primitive_host_0309_semantics
  · exact primitive_host_0310_semantics
  · exact primitive_host_0311_semantics

end InducedPentagons.Paper

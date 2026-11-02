import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData024
import InducedPentagonsPaper.Generated.PrimitiveRows016

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0288 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7165) = [22, 0, 0, 0, 0, 60, 138, 114, 0, 60, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0288_semantics :
    (Generated.hostChunk024[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[0]).mask = 7165 := by decide +kernel
  have hv : (Generated.hostChunk024[0]).primitive.toList = [22, 0, 0, 0, 0, 60, 138, 114, 0, 60, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0288]
  rfl

theorem primitive_values_0289 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7166) = [22, 0, 0, 0, 0, 58, 120, 112, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0289_semantics :
    (Generated.hostChunk024[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[1]).mask = 7166 := by decide +kernel
  have hv : (Generated.hostChunk024[1]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 112, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0289]
  rfl

theorem primitive_values_0290 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7167) = [24, 0, 0, 0, 0, 76, 216, 160, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0290_semantics :
    (Generated.hostChunk024[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[2]).mask = 7167 := by decide +kernel
  have hv : (Generated.hostChunk024[2]).primitive.toList = [24, 0, 0, 0, 0, 76, 216, 160, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0290]
  rfl

theorem primitive_values_0291 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7740) = [16, 0, 0, 0, 0, 24, 24, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0291_semantics :
    (Generated.hostChunk024[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[3]).mask = 7740 := by decide +kernel
  have hv : (Generated.hostChunk024[3]).primitive.toList = [16, 0, 0, 0, 0, 24, 24, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0291]
  rfl

theorem primitive_values_0292 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7741) = [18, 0, 0, 0, 0, 36, 66, 48, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0292_semantics :
    (Generated.hostChunk024[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[4]).mask = 7741 := by decide +kernel
  have hv : (Generated.hostChunk024[4]).primitive.toList = [18, 0, 0, 0, 0, 36, 66, 48, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0292]
  rfl

theorem primitive_values_0293 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7743) = [20, 0, 0, 0, 0, 50, 132, 72, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0293_semantics :
    (Generated.hostChunk024[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[5]).mask = 7743 := by decide +kernel
  have hv : (Generated.hostChunk024[5]).primitive.toList = [20, 0, 0, 0, 0, 50, 132, 72, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0293]
  rfl

theorem primitive_values_0294 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7804) = [18, 40, 32, 16, 0, 32, 36, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0294_semantics :
    (Generated.hostChunk024[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[6]).mask = 7804 := by decide +kernel
  have hv : (Generated.hostChunk024[6]).primitive.toList = [18, 40, 32, 16, 0, 32, 36, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0294]
  rfl

theorem primitive_values_0295 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7805) = [20, 0, 0, 0, 0, 46, 90, 76, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0295_semantics :
    (Generated.hostChunk024[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[7]).mask = 7805 := by decide +kernel
  have hv : (Generated.hostChunk024[7]).primitive.toList = [20, 0, 0, 0, 0, 46, 90, 76, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0295]
  rfl

theorem primitive_values_0296 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7807) = [22, 0, 0, 0, 0, 62, 168, 112, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0296_semantics :
    (Generated.hostChunk024[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[8]).mask = 7807 := by decide +kernel
  have hv : (Generated.hostChunk024[8]).primitive.toList = [22, 0, 0, 0, 0, 62, 168, 112, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0296]
  rfl

theorem primitive_values_0297 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7860) = [16, 0, 0, 0, 0, 24, 18, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0297_semantics :
    (Generated.hostChunk024[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[9]).mask = 7860 := by decide +kernel
  have hv : (Generated.hostChunk024[9]).primitive.toList = [16, 0, 0, 0, 0, 24, 18, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0297]
  rfl

theorem primitive_values_0298 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7861) = [18, 0, 0, 0, 0, 36, 54, 52, 0, 26, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0298_semantics :
    (Generated.hostChunk024[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[10]).mask = 7861 := by decide +kernel
  have hv : (Generated.hostChunk024[10]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 52, 0, 26, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0298]
  rfl

theorem primitive_values_0299 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7862) = [18, 0, 0, 0, 0, 34, 42, 54, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0299_semantics :
    (Generated.hostChunk024[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk024[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk024[11]).mask = 7862 := by decide +kernel
  have hv : (Generated.hostChunk024[11]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 54, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0299]
  rfl

theorem primitive_chunk_024_semantics :
    ∀ h ∈ Generated.hostChunk024.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk024.toList = [Generated.hostChunk024[0], Generated.hostChunk024[1], Generated.hostChunk024[2], Generated.hostChunk024[3], Generated.hostChunk024[4], Generated.hostChunk024[5], Generated.hostChunk024[6], Generated.hostChunk024[7], Generated.hostChunk024[8], Generated.hostChunk024[9], Generated.hostChunk024[10], Generated.hostChunk024[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0288_semantics
  · exact primitive_host_0289_semantics
  · exact primitive_host_0290_semantics
  · exact primitive_host_0291_semantics
  · exact primitive_host_0292_semantics
  · exact primitive_host_0293_semantics
  · exact primitive_host_0294_semantics
  · exact primitive_host_0295_semantics
  · exact primitive_host_0296_semantics
  · exact primitive_host_0297_semantics
  · exact primitive_host_0298_semantics
  · exact primitive_host_0299_semantics

end InducedPentagons.Paper

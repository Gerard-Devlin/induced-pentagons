import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData028
import InducedPentagonsPaper.Generated.PrimitiveRows020

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0336 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15356) = [22, 0, 0, 0, 0, 54, 90, 108, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0336_semantics :
    (Generated.hostChunk028[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[0]).mask = 15356 := by decide +kernel
  have hv : (Generated.hostChunk028[0]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 108, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0336]
  rfl

theorem primitive_values_0337 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15357) = [24, 0, 0, 0, 0, 70, 162, 152, 0, 78, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0337_semantics :
    (Generated.hostChunk028[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[1]).mask = 15357 := by decide +kernel
  have hv : (Generated.hostChunk028[1]).primitive.toList = [24, 0, 0, 0, 0, 70, 162, 152, 0, 78, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0337]
  rfl

theorem primitive_values_0338 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15359) = [26, 0, 0, 0, 0, 88, 258, 208, 0, 158, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0338_semantics :
    (Generated.hostChunk028[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[2]).mask = 15359 := by decide +kernel
  have hv : (Generated.hostChunk028[2]).primitive.toList = [26, 0, 0, 0, 0, 88, 258, 208, 0, 158, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0338]
  rfl

theorem primitive_values_0339 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15796) = [18, 0, 0, 0, 0, 30, 24, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0339_semantics :
    (Generated.hostChunk028[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[3]).mask = 15796 := by decide +kernel
  have hv : (Generated.hostChunk028[3]).primitive.toList = [18, 0, 0, 0, 0, 30, 24, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0339]
  rfl

theorem primitive_values_0340 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15797) = [20, 10, 10, 8, 0, 42, 60, 70, 0, 18, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0340_semantics :
    (Generated.hostChunk028[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[4]).mask = 15797 := by decide +kernel
  have hv : (Generated.hostChunk028[4]).primitive.toList = [20, 10, 10, 8, 0, 42, 60, 70, 0, 18, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0340]
  rfl

theorem primitive_values_0341 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15799) = [22, 0, 0, 0, 0, 56, 114, 104, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0341_semantics :
    (Generated.hostChunk028[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[5]).mask = 15799 := by decide +kernel
  have hv : (Generated.hostChunk028[5]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 104, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0341]
  rfl

theorem primitive_values_0342 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15804) = [20, 0, 0, 0, 0, 40, 48, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0342_semantics :
    (Generated.hostChunk028[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[6]).mask = 15804 := by decide +kernel
  have hv : (Generated.hostChunk028[6]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0342]
  rfl

theorem primitive_values_0343 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15805) = [22, 0, 0, 0, 0, 54, 102, 104, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0343_semantics :
    (Generated.hostChunk028[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[7]).mask = 15805 := by decide +kernel
  have hv : (Generated.hostChunk028[7]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 104, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0343]
  rfl

theorem primitive_values_0344 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15807) = [24, 0, 0, 0, 0, 70, 180, 144, 0, 80, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0344_semantics :
    (Generated.hostChunk028[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[8]).mask = 15807 := by decide +kernel
  have hv : (Generated.hostChunk028[8]).primitive.toList = [24, 0, 0, 0, 0, 70, 180, 144, 0, 80, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0344]
  rfl

theorem primitive_values_0345 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15863) = [24, 0, 0, 0, 0, 72, 186, 150, 0, 96, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0345_semantics :
    (Generated.hostChunk028[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[9]).mask = 15863 := by decide +kernel
  have hv : (Generated.hostChunk028[9]).primitive.toList = [24, 0, 0, 0, 0, 72, 186, 150, 0, 96, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0345]
  rfl

theorem primitive_values_0346 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15868) = [22, 10, 12, 12, 0, 52, 84, 102, 0, 20, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0346_semantics :
    (Generated.hostChunk028[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[10]).mask = 15868 := by decide +kernel
  have hv : (Generated.hostChunk028[10]).primitive.toList = [22, 10, 12, 12, 0, 52, 84, 102, 0, 20, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0346]
  rfl

theorem primitive_values_0347 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15869) = [24, 0, 0, 0, 0, 68, 156, 144, 0, 64, 24, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0347_semantics :
    (Generated.hostChunk028[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk028[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk028[11]).mask = 15869 := by decide +kernel
  have hv : (Generated.hostChunk028[11]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 144, 0, 64, 24, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0347]
  rfl

theorem primitive_chunk_028_semantics :
    ∀ h ∈ Generated.hostChunk028.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk028.toList = [Generated.hostChunk028[0], Generated.hostChunk028[1], Generated.hostChunk028[2], Generated.hostChunk028[3], Generated.hostChunk028[4], Generated.hostChunk028[5], Generated.hostChunk028[6], Generated.hostChunk028[7], Generated.hostChunk028[8], Generated.hostChunk028[9], Generated.hostChunk028[10], Generated.hostChunk028[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0336_semantics
  · exact primitive_host_0337_semantics
  · exact primitive_host_0338_semantics
  · exact primitive_host_0339_semantics
  · exact primitive_host_0340_semantics
  · exact primitive_host_0341_semantics
  · exact primitive_host_0342_semantics
  · exact primitive_host_0343_semantics
  · exact primitive_host_0344_semantics
  · exact primitive_host_0345_semantics
  · exact primitive_host_0346_semantics
  · exact primitive_host_0347_semantics

end InducedPentagons.Paper

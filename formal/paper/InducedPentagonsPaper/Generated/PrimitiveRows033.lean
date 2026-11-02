import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData033
import InducedPentagonsPaper.Generated.PrimitiveRows025

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0396 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39526) = [16, 0, 0, 0, 0, 28, 36, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0396_semantics :
    (Generated.hostChunk033[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[0]).mask = 39526 := by decide +kernel
  have hv : (Generated.hostChunk033[0]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0396]
  rfl

theorem primitive_values_0397 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39527) = [18, 0, 0, 0, 0, 38, 60, 58, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0397_semantics :
    (Generated.hostChunk033[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[1]).mask = 39527 := by decide +kernel
  have hv : (Generated.hostChunk033[1]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 58, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0397]
  rfl

theorem primitive_values_0398 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39532) = [16, 0, 0, 0, 0, 26, 24, 32, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0398_semantics :
    (Generated.hostChunk033[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[2]).mask = 39532 := by decide +kernel
  have hv : (Generated.hostChunk033[2]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 32, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0398]
  rfl

theorem primitive_values_0399 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39533) = [18, 0, 0, 0, 0, 36, 48, 56, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0399_semantics :
    (Generated.hostChunk033[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[3]).mask = 39533 := by decide +kernel
  have hv : (Generated.hostChunk033[3]).primitive.toList = [18, 0, 0, 0, 0, 36, 48, 56, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0399]
  rfl

theorem primitive_values_0400 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39534) = [18, 0, 0, 0, 0, 38, 60, 56, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0400_semantics :
    (Generated.hostChunk033[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[4]).mask = 39534 := by decide +kernel
  have hv : (Generated.hostChunk033[4]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 56, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0400]
  rfl

theorem primitive_values_0401 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39535) = [20, 0, 0, 0, 0, 50, 102, 86, 0, 54, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0401_semantics :
    (Generated.hostChunk033[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[5]).mask = 39535 := by decide +kernel
  have hv : (Generated.hostChunk033[5]).primitive.toList = [20, 0, 0, 0, 0, 50, 102, 86, 0, 54, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0401]
  rfl

theorem primitive_values_0402 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39536) = [14, 0, 0, 0, 0, 16, 6, 12, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0402_semantics :
    (Generated.hostChunk033[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[6]).mask = 39536 := by decide +kernel
  have hv : (Generated.hostChunk033[6]).primitive.toList = [14, 0, 0, 0, 0, 16, 6, 12, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0402]
  rfl

theorem primitive_values_0403 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39537) = [16, 0, 0, 0, 0, 24, 18, 22, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0403_semantics :
    (Generated.hostChunk033[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[7]).mask = 39537 := by decide +kernel
  have hv : (Generated.hostChunk033[7]).primitive.toList = [16, 0, 0, 0, 0, 24, 18, 22, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0403]
  rfl

theorem primitive_values_0404 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39538) = [16, 0, 0, 0, 0, 26, 30, 32, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0404_semantics :
    (Generated.hostChunk033[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[8]).mask = 39538 := by decide +kernel
  have hv : (Generated.hostChunk033[8]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 32, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0404]
  rfl

theorem primitive_values_0405 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39539) = [18, 0, 0, 0, 0, 36, 54, 48, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0405_semantics :
    (Generated.hostChunk033[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[9]).mask = 39539 := by decide +kernel
  have hv : (Generated.hostChunk033[9]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 48, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0405]
  rfl

theorem primitive_values_0406 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39540) = [16, 10, 6, 0, 0, 24, 18, 28, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0406_semantics :
    (Generated.hostChunk033[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[10]).mask = 39540 := by decide +kernel
  have hv : (Generated.hostChunk033[10]).primitive.toList = [16, 10, 6, 0, 0, 24, 18, 28, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0406]
  rfl

theorem primitive_values_0407 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39541) = [18, 0, 0, 0, 0, 34, 42, 46, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0407_semantics :
    (Generated.hostChunk033[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk033[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk033[11]).mask = 39541 := by decide +kernel
  have hv : (Generated.hostChunk033[11]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 46, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0407]
  rfl

theorem primitive_chunk_033_semantics :
    ∀ h ∈ Generated.hostChunk033.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk033.toList = [Generated.hostChunk033[0], Generated.hostChunk033[1], Generated.hostChunk033[2], Generated.hostChunk033[3], Generated.hostChunk033[4], Generated.hostChunk033[5], Generated.hostChunk033[6], Generated.hostChunk033[7], Generated.hostChunk033[8], Generated.hostChunk033[9], Generated.hostChunk033[10], Generated.hostChunk033[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0396_semantics
  · exact primitive_host_0397_semantics
  · exact primitive_host_0398_semantics
  · exact primitive_host_0399_semantics
  · exact primitive_host_0400_semantics
  · exact primitive_host_0401_semantics
  · exact primitive_host_0402_semantics
  · exact primitive_host_0403_semantics
  · exact primitive_host_0404_semantics
  · exact primitive_host_0405_semantics
  · exact primitive_host_0406_semantics
  · exact primitive_host_0407_semantics

end InducedPentagons.Paper

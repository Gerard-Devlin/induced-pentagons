import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData035
import InducedPentagonsPaper.Generated.PrimitiveRows027

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0420 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39655) = [20, 0, 0, 0, 0, 50, 96, 90, 0, 56, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0420_semantics :
    (Generated.hostChunk035[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[0]).mask = 39655 := by decide +kernel
  have hv : (Generated.hostChunk035[0]).primitive.toList = [20, 0, 0, 0, 0, 50, 96, 90, 0, 56, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0420]
  rfl

theorem primitive_values_0421 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39658) = [18, 0, 0, 0, 0, 36, 48, 54, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0421_semantics :
    (Generated.hostChunk035[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[1]).mask = 39658 := by decide +kernel
  have hv : (Generated.hostChunk035[1]).primitive.toList = [18, 0, 0, 0, 0, 36, 48, 54, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0421]
  rfl

theorem primitive_values_0422 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39659) = [20, 0, 0, 0, 0, 48, 84, 86, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0422_semantics :
    (Generated.hostChunk035[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[2]).mask = 39659 := by decide +kernel
  have hv : (Generated.hostChunk035[2]).primitive.toList = [20, 0, 0, 0, 0, 48, 84, 86, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0422]
  rfl

theorem primitive_values_0423 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39662) = [20, 0, 0, 0, 0, 48, 84, 84, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0423_semantics :
    (Generated.hostChunk035[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[3]).mask = 39662 := by decide +kernel
  have hv : (Generated.hostChunk035[3]).primitive.toList = [20, 0, 0, 0, 0, 48, 84, 84, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0423]
  rfl

theorem primitive_values_0424 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39663) = [22, 0, 0, 0, 0, 62, 138, 124, 0, 88, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0424_semantics :
    (Generated.hostChunk035[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[4]).mask = 39663 := by decide +kernel
  have hv : (Generated.hostChunk035[4]).primitive.toList = [22, 0, 0, 0, 0, 62, 138, 124, 0, 88, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0424]
  rfl

theorem primitive_values_0425 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39664) = [16, 0, 0, 0, 0, 24, 18, 26, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0425_semantics :
    (Generated.hostChunk035[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[5]).mask = 39664 := by decide +kernel
  have hv : (Generated.hostChunk035[5]).primitive.toList = [16, 0, 0, 0, 0, 24, 18, 26, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0425]
  rfl

theorem primitive_values_0426 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39665) = [18, 0, 0, 0, 0, 34, 42, 44, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0426_semantics :
    (Generated.hostChunk035[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[6]).mask = 39665 := by decide +kernel
  have hv : (Generated.hostChunk035[6]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 44, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0426]
  rfl

theorem primitive_values_0427 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39666) = [18, 0, 0, 0, 0, 34, 42, 50, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0427_semantics :
    (Generated.hostChunk035[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[7]).mask = 39666 := by decide +kernel
  have hv : (Generated.hostChunk035[7]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 50, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0427]
  rfl

theorem primitive_values_0428 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39667) = [20, 0, 0, 0, 0, 46, 78, 76, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0428_semantics :
    (Generated.hostChunk035[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[8]).mask = 39667 := by decide +kernel
  have hv : (Generated.hostChunk035[8]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 76, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0428]
  rfl

theorem primitive_values_0429 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39670) = [20, 0, 0, 0, 0, 46, 78, 82, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0429_semantics :
    (Generated.hostChunk035[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[9]).mask = 39670 := by decide +kernel
  have hv : (Generated.hostChunk035[9]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 82, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0429]
  rfl

theorem primitive_values_0430 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39671) = [22, 0, 0, 0, 0, 60, 132, 116, 0, 72, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0430_semantics :
    (Generated.hostChunk035[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[10]).mask = 39671 := by decide +kernel
  have hv : (Generated.hostChunk035[10]).primitive.toList = [22, 0, 0, 0, 0, 60, 132, 116, 0, 72, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0430]
  rfl

theorem primitive_values_0431 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39672) = [18, 20, 16, 0, 0, 32, 30, 44, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0431_semantics :
    (Generated.hostChunk035[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk035[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk035[11]).mask = 39672 := by decide +kernel
  have hv : (Generated.hostChunk035[11]).primitive.toList = [18, 20, 16, 0, 0, 32, 30, 44, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0431]
  rfl

theorem primitive_chunk_035_semantics :
    ∀ h ∈ Generated.hostChunk035.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk035.toList = [Generated.hostChunk035[0], Generated.hostChunk035[1], Generated.hostChunk035[2], Generated.hostChunk035[3], Generated.hostChunk035[4], Generated.hostChunk035[5], Generated.hostChunk035[6], Generated.hostChunk035[7], Generated.hostChunk035[8], Generated.hostChunk035[9], Generated.hostChunk035[10], Generated.hostChunk035[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0420_semantics
  · exact primitive_host_0421_semantics
  · exact primitive_host_0422_semantics
  · exact primitive_host_0423_semantics
  · exact primitive_host_0424_semantics
  · exact primitive_host_0425_semantics
  · exact primitive_host_0426_semantics
  · exact primitive_host_0427_semantics
  · exact primitive_host_0428_semantics
  · exact primitive_host_0429_semantics
  · exact primitive_host_0430_semantics
  · exact primitive_host_0431_semantics

end InducedPentagons.Paper

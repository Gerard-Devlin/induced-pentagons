import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData061
import InducedPentagonsPaper.Generated.PrimitiveRows053

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0732 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 58995) = [20, 0, 0, 0, 0, 48, 84, 84, 0, 72, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0732_semantics :
    (Generated.hostChunk061[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[0]).mask = 58995 := by decide +kernel
  have hv : (Generated.hostChunk061[0]).primitive.toList = [20, 0, 0, 0, 0, 48, 84, 84, 0, 72, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0732]
  rfl

theorem primitive_values_0733 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 58997) = [20, 0, 0, 0, 0, 44, 66, 76, 0, 36, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0733_semantics :
    (Generated.hostChunk061[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[1]).mask = 58997 := by decide +kernel
  have hv : (Generated.hostChunk061[1]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 76, 0, 36, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0733]
  rfl

theorem primitive_values_0734 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 58999) = [22, 0, 0, 0, 0, 58, 120, 112, 0, 82, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0734_semantics :
    (Generated.hostChunk061[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[2]).mask = 58999 := by decide +kernel
  have hv : (Generated.hostChunk061[2]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 112, 0, 82, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0734]
  rfl

theorem primitive_values_0735 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59004) = [20, 0, 0, 0, 0, 40, 48, 60, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0735_semantics :
    (Generated.hostChunk061[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[3]).mask = 59004 := by decide +kernel
  have hv : (Generated.hostChunk061[3]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 60, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0735]
  rfl

theorem primitive_values_0736 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59005) = [22, 0, 0, 0, 0, 54, 102, 96, 0, 46, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0736_semantics :
    (Generated.hostChunk061[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[4]).mask = 59005 := by decide +kernel
  have hv : (Generated.hostChunk061[4]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 96, 0, 46, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0736]
  rfl

theorem primitive_values_0737 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59007) = [24, 0, 0, 0, 0, 70, 180, 140, 0, 100, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0737_semantics :
    (Generated.hostChunk061[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[5]).mask = 59007 := by decide +kernel
  have hv : (Generated.hostChunk061[5]).primitive.toList = [24, 0, 0, 0, 0, 70, 180, 140, 0, 100, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0737]
  rfl

theorem primitive_values_0738 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59063) = [22, 0, 0, 0, 0, 56, 108, 110, 0, 56, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0738_semantics :
    (Generated.hostChunk061[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[6]).mask = 59063 := by decide +kernel
  have hv : (Generated.hostChunk061[6]).primitive.toList = [22, 0, 0, 0, 0, 56, 108, 110, 0, 56, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0738]
  rfl

theorem primitive_values_0739 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59065) = [20, 0, 0, 0, 0, 42, 60, 76, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0739_semantics :
    (Generated.hostChunk061[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[7]).mask = 59065 := by decide +kernel
  have hv : (Generated.hostChunk061[7]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 76, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0739]
  rfl

theorem primitive_values_0740 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59066) = [20, 20, 16, 8, 16, 40, 48, 68, 8, 16, 4, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0740_semantics :
    (Generated.hostChunk061[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[8]).mask = 59066 := by decide +kernel
  have hv : (Generated.hostChunk061[8]).primitive.toList = [20, 20, 16, 8, 16, 40, 48, 68, 8, 16, 4, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0740]
  rfl

theorem primitive_values_0741 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59067) = [22, 0, 0, 0, 0, 54, 102, 104, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 16] := by
  decide +kernel

theorem primitive_host_0741_semantics :
    (Generated.hostChunk061[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[9]).mask = 59067 := by decide +kernel
  have hv : (Generated.hostChunk061[9]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 104, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0741]
  rfl

theorem primitive_values_0742 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59069) = [22, 0, 0, 0, 0, 54, 102, 104, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0742_semantics :
    (Generated.hostChunk061[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[10]).mask = 59069 := by decide +kernel
  have hv : (Generated.hostChunk061[10]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 104, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0742]
  rfl

theorem primitive_values_0743 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59070) = [22, 0, 0, 0, 0, 52, 90, 98, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0743_semantics :
    (Generated.hostChunk061[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk061[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk061[11]).mask = 59070 := by decide +kernel
  have hv : (Generated.hostChunk061[11]).primitive.toList = [22, 0, 0, 0, 0, 52, 90, 98, 0, 28, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0743]
  rfl

theorem primitive_chunk_061_semantics :
    ∀ h ∈ Generated.hostChunk061.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk061.toList = [Generated.hostChunk061[0], Generated.hostChunk061[1], Generated.hostChunk061[2], Generated.hostChunk061[3], Generated.hostChunk061[4], Generated.hostChunk061[5], Generated.hostChunk061[6], Generated.hostChunk061[7], Generated.hostChunk061[8], Generated.hostChunk061[9], Generated.hostChunk061[10], Generated.hostChunk061[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0732_semantics
  · exact primitive_host_0733_semantics
  · exact primitive_host_0734_semantics
  · exact primitive_host_0735_semantics
  · exact primitive_host_0736_semantics
  · exact primitive_host_0737_semantics
  · exact primitive_host_0738_semantics
  · exact primitive_host_0739_semantics
  · exact primitive_host_0740_semantics
  · exact primitive_host_0741_semantics
  · exact primitive_host_0742_semantics
  · exact primitive_host_0743_semantics

end InducedPentagons.Paper

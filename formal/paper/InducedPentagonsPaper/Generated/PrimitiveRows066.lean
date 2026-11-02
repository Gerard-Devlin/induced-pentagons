import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData066
import InducedPentagonsPaper.Generated.PrimitiveRows058

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0792 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111595) = [24, 0, 0, 0, 0, 68, 144, 148, 0, 88, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0792_semantics :
    (Generated.hostChunk066[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[0]).mask = 111595 := by decide +kernel
  have hv : (Generated.hostChunk066[0]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 148, 0, 88, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0792]
  rfl

theorem primitive_values_0793 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111598) = [24, 0, 0, 0, 0, 66, 126, 144, 0, 68, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0793_semantics :
    (Generated.hostChunk066[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[1]).mask = 111598 := by decide +kernel
  have hv : (Generated.hostChunk066[1]).primitive.toList = [24, 0, 0, 0, 0, 66, 126, 144, 0, 68, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0793]
  rfl

theorem primitive_values_0794 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111599) = [26, 0, 0, 0, 0, 82, 198, 198, 0, 128, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0794_semantics :
    (Generated.hostChunk066[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[2]).mask = 111599 := by decide +kernel
  have hv : (Generated.hostChunk066[2]).primitive.toList = [26, 0, 0, 0, 0, 82, 198, 198, 0, 128, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0794]
  rfl

theorem primitive_values_0795 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111614) = [26, 0, 0, 0, 0, 80, 180, 192, 0, 104, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0795_semantics :
    (Generated.hostChunk066[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[3]).mask = 111614 := by decide +kernel
  have hv : (Generated.hostChunk066[3]).primitive.toList = [26, 0, 0, 0, 0, 80, 180, 192, 0, 104, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0795]
  rfl

theorem primitive_values_0796 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111615) = [28, 0, 0, 0, 0, 98, 276, 256, 0, 192, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by
  decide +kernel

theorem primitive_host_0796_semantics :
    (Generated.hostChunk066[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[4]).mask = 111615 := by decide +kernel
  have hv : (Generated.hostChunk066[4]).primitive.toList = [28, 0, 0, 0, 0, 98, 276, 256, 0, 192, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by decide +kernel
  rw [hm, hv, primitive_values_0796]
  rfl

theorem primitive_values_0797 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111979) = [22, 0, 0, 0, 0, 54, 96, 104, 0, 56, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0797_semantics :
    (Generated.hostChunk066[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[5]).mask = 111979 := by decide +kernel
  have hv : (Generated.hostChunk066[5]).primitive.toList = [22, 0, 0, 0, 0, 54, 96, 104, 0, 56, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0797]
  rfl

theorem primitive_values_0798 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111980) = [20, 0, 0, 0, 0, 40, 48, 68, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0798_semantics :
    (Generated.hostChunk066[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[6]).mask = 111980 := by decide +kernel
  have hv : (Generated.hostChunk066[6]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 68, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0798]
  rfl

theorem primitive_values_0799 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111981) = [22, 10, 12, 8, 0, 52, 84, 98, 0, 40, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0799_semantics :
    (Generated.hostChunk066[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[7]).mask = 111981 := by decide +kernel
  have hv : (Generated.hostChunk066[7]).primitive.toList = [22, 10, 12, 8, 0, 52, 84, 98, 0, 40, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0799]
  rfl

theorem primitive_values_0800 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111982) = [22, 0, 0, 0, 0, 52, 84, 104, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0800_semantics :
    (Generated.hostChunk066[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[8]).mask = 111982 := by decide +kernel
  have hv : (Generated.hostChunk066[8]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 104, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0800]
  rfl

theorem primitive_values_0801 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111983) = [24, 0, 0, 0, 0, 66, 138, 142, 0, 76, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0801_semantics :
    (Generated.hostChunk066[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[9]).mask = 111983 := by decide +kernel
  have hv : (Generated.hostChunk066[9]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 142, 0, 76, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0801]
  rfl

theorem primitive_values_0802 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111988) = [20, 20, 16, 0, 16, 38, 36, 60, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0802_semantics :
    (Generated.hostChunk066[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[10]).mask = 111988 := by decide +kernel
  have hv : (Generated.hostChunk066[10]).primitive.toList = [20, 20, 16, 0, 16, 38, 36, 60, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0802]
  rfl

theorem primitive_values_0803 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111989) = [22, 0, 0, 0, 0, 50, 72, 92, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0803_semantics :
    (Generated.hostChunk066[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk066[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk066[11]).mask = 111989 := by decide +kernel
  have hv : (Generated.hostChunk066[11]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 92, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0803]
  rfl

theorem primitive_chunk_066_semantics :
    ∀ h ∈ Generated.hostChunk066.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk066.toList = [Generated.hostChunk066[0], Generated.hostChunk066[1], Generated.hostChunk066[2], Generated.hostChunk066[3], Generated.hostChunk066[4], Generated.hostChunk066[5], Generated.hostChunk066[6], Generated.hostChunk066[7], Generated.hostChunk066[8], Generated.hostChunk066[9], Generated.hostChunk066[10], Generated.hostChunk066[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0792_semantics
  · exact primitive_host_0793_semantics
  · exact primitive_host_0794_semantics
  · exact primitive_host_0795_semantics
  · exact primitive_host_0796_semantics
  · exact primitive_host_0797_semantics
  · exact primitive_host_0798_semantics
  · exact primitive_host_0799_semantics
  · exact primitive_host_0800_semantics
  · exact primitive_host_0801_semantics
  · exact primitive_host_0802_semantics
  · exact primitive_host_0803_semantics

end InducedPentagons.Paper

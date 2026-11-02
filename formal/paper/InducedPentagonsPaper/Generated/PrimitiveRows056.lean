import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData056
import InducedPentagonsPaper.Generated.PrimitiveRows048

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0672 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48575) = [26, 0, 0, 0, 0, 82, 216, 188, 0, 128, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by
  decide +kernel

theorem primitive_host_0672_semantics :
    (Generated.hostChunk056[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[0]).mask = 48575 := by decide +kernel
  have hv : (Generated.hostChunk056[0]).primitive.toList = [26, 0, 0, 0, 0, 82, 216, 188, 0, 128, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by decide +kernel
  rw [hm, hv, primitive_values_0672]
  rfl

theorem primitive_values_0673 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48624) = [20, 10, 8, 8, 8, 42, 60, 66, 8, 36, 0, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0673_semantics :
    (Generated.hostChunk056[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[1]).mask = 48624 := by decide +kernel
  have hv : (Generated.hostChunk056[1]).primitive.toList = [20, 10, 8, 8, 8, 42, 60, 66, 8, 36, 0, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0673]
  rfl

theorem primitive_values_0674 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48625) = [22, 0, 0, 0, 0, 54, 102, 96, 0, 50, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0674_semantics :
    (Generated.hostChunk056[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[2]).mask = 48625 := by decide +kernel
  have hv : (Generated.hostChunk056[2]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 96, 0, 50, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0674]
  rfl

theorem primitive_values_0675 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48627) = [24, 0, 0, 0, 0, 68, 156, 138, 0, 84, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0675_semantics :
    (Generated.hostChunk056[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[3]).mask = 48627 := by decide +kernel
  have hv : (Generated.hostChunk056[3]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 138, 0, 84, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0675]
  rfl

theorem primitive_values_0676 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48628) = [22, 10, 10, 8, 10, 52, 84, 98, 8, 42, 0, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0676_semantics :
    (Generated.hostChunk056[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[4]).mask = 48628 := by decide +kernel
  have hv : (Generated.hostChunk056[4]).primitive.toList = [22, 10, 10, 8, 10, 52, 84, 98, 8, 42, 0, 0, 0, 24, 4, 0, 8, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0676]
  rfl

theorem primitive_values_0677 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48629) = [24, 0, 0, 0, 0, 66, 138, 138, 0, 72, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0677_semantics :
    (Generated.hostChunk056[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[5]).mask = 48629 := by decide +kernel
  have hv : (Generated.hostChunk056[5]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 138, 0, 72, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0677]
  rfl

theorem primitive_values_0678 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48631) = [26, 0, 0, 0, 0, 82, 210, 190, 0, 128, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by
  decide +kernel

theorem primitive_host_0678_semantics :
    (Generated.hostChunk056[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[6]).mask = 48631 := by decide +kernel
  have hv : (Generated.hostChunk056[6]).primitive.toList = [26, 0, 0, 0, 0, 82, 210, 190, 0, 128, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by decide +kernel
  rw [hm, hv, primitive_values_0678]
  rfl

theorem primitive_values_0679 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48636) = [24, 10, 12, 12, 12, 64, 120, 138, 12, 60, 8, 0, 0, 24, 4, 0, 12, 4, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0679_semantics :
    (Generated.hostChunk056[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[7]).mask = 48636 := by decide +kernel
  have hv : (Generated.hostChunk056[7]).primitive.toList = [24, 10, 12, 12, 12, 64, 120, 138, 12, 60, 8, 0, 0, 24, 4, 0, 12, 4, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0679]
  rfl

theorem primitive_values_0680 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48637) = [26, 0, 0, 0, 0, 80, 192, 188, 0, 112, 20, 0, 0, 48, 0, 4, 0, 0, 2, 2, 0, 68] := by
  decide +kernel

theorem primitive_host_0680_semantics :
    (Generated.hostChunk056[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[8]).mask = 48637 := by decide +kernel
  have hv : (Generated.hostChunk056[8]).primitive.toList = [26, 0, 0, 0, 0, 80, 192, 188, 0, 112, 20, 0, 0, 48, 0, 4, 0, 0, 2, 2, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0680]
  rfl

theorem primitive_values_0681 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48639) = [28, 0, 0, 0, 0, 98, 288, 250, 0, 196, 24, 0, 0, 120, 0, 0, 0, 0, 0, 0, 4, 144] := by
  decide +kernel

theorem primitive_host_0681_semantics :
    (Generated.hostChunk056[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[9]).mask = 48639 := by decide +kernel
  have hv : (Generated.hostChunk056[9]).primitive.toList = [28, 0, 0, 0, 0, 98, 288, 250, 0, 196, 24, 0, 0, 120, 0, 0, 0, 0, 0, 0, 4, 144] := by decide +kernel
  rw [hm, hv, primitive_values_0681]
  rfl

theorem primitive_values_0682 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48689) = [18, 0, 0, 0, 0, 30, 24, 32, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0682_semantics :
    (Generated.hostChunk056[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[10]).mask = 48689 := by decide +kernel
  have hv : (Generated.hostChunk056[10]).primitive.toList = [18, 0, 0, 0, 0, 30, 24, 32, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0682]
  rfl

theorem primitive_values_0683 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48690) = [18, 0, 0, 0, 0, 32, 36, 44, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0683_semantics :
    (Generated.hostChunk056[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk056[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk056[11]).mask = 48690 := by decide +kernel
  have hv : (Generated.hostChunk056[11]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 44, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0683]
  rfl

theorem primitive_chunk_056_semantics :
    ∀ h ∈ Generated.hostChunk056.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk056.toList = [Generated.hostChunk056[0], Generated.hostChunk056[1], Generated.hostChunk056[2], Generated.hostChunk056[3], Generated.hostChunk056[4], Generated.hostChunk056[5], Generated.hostChunk056[6], Generated.hostChunk056[7], Generated.hostChunk056[8], Generated.hostChunk056[9], Generated.hostChunk056[10], Generated.hostChunk056[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0672_semantics
  · exact primitive_host_0673_semantics
  · exact primitive_host_0674_semantics
  · exact primitive_host_0675_semantics
  · exact primitive_host_0676_semantics
  · exact primitive_host_0677_semantics
  · exact primitive_host_0678_semantics
  · exact primitive_host_0679_semantics
  · exact primitive_host_0680_semantics
  · exact primitive_host_0681_semantics
  · exact primitive_host_0682_semantics
  · exact primitive_host_0683_semantics

end InducedPentagons.Paper

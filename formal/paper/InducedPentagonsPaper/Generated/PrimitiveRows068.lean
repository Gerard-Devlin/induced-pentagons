import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData068
import InducedPentagonsPaper.Generated.PrimitiveRows060

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0816 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112638) = [28, 0, 0, 0, 0, 90, 216, 232, 0, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0816_semantics :
    (Generated.hostChunk068[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[0]).mask = 112638 := by decide +kernel
  have hv : (Generated.hostChunk068[0]).primitive.toList = [28, 0, 0, 0, 0, 90, 216, 232, 0, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0816]
  rfl

theorem primitive_values_0817 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 112639) = [30, 0, 0, 0, 0, 110, 336, 304, 0, 224, 56, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 152] := by
  decide +kernel

theorem primitive_host_0817_semantics :
    (Generated.hostChunk068[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[1]).mask = 112639 := by decide +kernel
  have hv : (Generated.hostChunk068[1]).primitive.toList = [30, 0, 0, 0, 0, 110, 336, 304, 0, 224, 56, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 152] := by decide +kernel
  rw [hm, hv, primitive_values_0817]
  rfl

theorem primitive_values_0818 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113631) = [28, 0, 0, 0, 0, 104, 288, 288, 0, 264, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by
  decide +kernel

theorem primitive_host_0818_semantics :
    (Generated.hostChunk068[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[2]).mask = 113631 := by decide +kernel
  have hv : (Generated.hostChunk068[2]).primitive.toList = [28, 0, 0, 0, 0, 104, 288, 288, 0, 264, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by decide +kernel
  rw [hm, hv, primitive_values_0818]
  rfl

theorem primitive_values_0819 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113640) = [22, 0, 0, 0, 0, 56, 102, 108, 0, 78, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0819_semantics :
    (Generated.hostChunk068[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[3]).mask = 113640 := by decide +kernel
  have hv : (Generated.hostChunk068[3]).primitive.toList = [22, 0, 0, 0, 0, 56, 102, 108, 0, 78, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0819]
  rfl

theorem primitive_values_0820 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113641) = [24, 0, 0, 0, 0, 68, 144, 146, 0, 100, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0820_semantics :
    (Generated.hostChunk068[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[4]).mask = 113641 := by decide +kernel
  have hv : (Generated.hostChunk068[4]).primitive.toList = [24, 0, 0, 0, 0, 68, 144, 146, 0, 100, 20, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0820]
  rfl

theorem primitive_values_0821 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113643) = [26, 0, 0, 0, 0, 82, 198, 196, 0, 142, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0821_semantics :
    (Generated.hostChunk068[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[5]).mask = 113643 := by decide +kernel
  have hv : (Generated.hostChunk068[5]).primitive.toList = [26, 0, 0, 0, 0, 82, 198, 196, 0, 142, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0821]
  rfl

theorem primitive_values_0822 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113647) = [28, 0, 0, 0, 0, 98, 270, 258, 0, 210, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0822_semantics :
    (Generated.hostChunk068[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[6]).mask = 113647 := by decide +kernel
  have hv : (Generated.hostChunk068[6]).primitive.toList = [28, 0, 0, 0, 0, 98, 270, 258, 0, 210, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0822]
  rfl

theorem primitive_values_0823 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113656) = [24, 0, 0, 0, 0, 66, 126, 144, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0823_semantics :
    (Generated.hostChunk068[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[7]).mask = 113656 := by decide +kernel
  have hv : (Generated.hostChunk068[7]).primitive.toList = [24, 0, 0, 0, 0, 66, 126, 144, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0823]
  rfl

theorem primitive_values_0824 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113657) = [26, 0, 0, 0, 0, 80, 180, 192, 0, 122, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0824_semantics :
    (Generated.hostChunk068[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[8]).mask = 113657 := by decide +kernel
  have hv : (Generated.hostChunk068[8]).primitive.toList = [26, 0, 0, 0, 0, 80, 180, 192, 0, 122, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0824]
  rfl

theorem primitive_values_0825 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113659) = [28, 0, 0, 0, 0, 96, 252, 252, 0, 186, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by
  decide +kernel

theorem primitive_host_0825_semantics :
    (Generated.hostChunk068[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[9]).mask = 113659 := by decide +kernel
  have hv : (Generated.hostChunk068[9]).primitive.toList = [28, 0, 0, 0, 0, 96, 252, 252, 0, 186, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by decide +kernel
  rw [hm, hv, primitive_values_0825]
  rfl

theorem primitive_values_0826 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113663) = [30, 0, 0, 0, 0, 114, 348, 324, 0, 282, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by
  decide +kernel

theorem primitive_host_0826_semantics :
    (Generated.hostChunk068[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[10]).mask = 113663 := by decide +kernel
  have hv : (Generated.hostChunk068[10]).primitive.toList = [30, 0, 0, 0, 0, 114, 348, 324, 0, 282, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by decide +kernel
  rw [hm, hv, primitive_values_0826]
  rfl

theorem primitive_values_0827 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 113961) = [20, 0, 0, 0, 0, 40, 48, 56, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0827_semantics :
    (Generated.hostChunk068[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk068[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk068[11]).mask = 113961 := by decide +kernel
  have hv : (Generated.hostChunk068[11]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 56, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0827]
  rfl

theorem primitive_chunk_068_semantics :
    ∀ h ∈ Generated.hostChunk068.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk068.toList = [Generated.hostChunk068[0], Generated.hostChunk068[1], Generated.hostChunk068[2], Generated.hostChunk068[3], Generated.hostChunk068[4], Generated.hostChunk068[5], Generated.hostChunk068[6], Generated.hostChunk068[7], Generated.hostChunk068[8], Generated.hostChunk068[9], Generated.hostChunk068[10], Generated.hostChunk068[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0816_semantics
  · exact primitive_host_0817_semantics
  · exact primitive_host_0818_semantics
  · exact primitive_host_0819_semantics
  · exact primitive_host_0820_semantics
  · exact primitive_host_0821_semantics
  · exact primitive_host_0822_semantics
  · exact primitive_host_0823_semantics
  · exact primitive_host_0824_semantics
  · exact primitive_host_0825_semantics
  · exact primitive_host_0826_semantics
  · exact primitive_host_0827_semantics

end InducedPentagons.Paper

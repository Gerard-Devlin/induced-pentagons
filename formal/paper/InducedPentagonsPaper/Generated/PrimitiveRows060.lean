import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData060
import InducedPentagonsPaper.Generated.PrimitiveRows052

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0720 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48893) = [26, 0, 0, 0, 0, 78, 180, 180, 0, 90, 36, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0720_semantics :
    (Generated.hostChunk060[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[0]).mask = 48893 := by decide +kernel
  have hv : (Generated.hostChunk060[0]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 180, 0, 90, 36, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0720]
  rfl

theorem primitive_values_0721 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48894) = [26, 0, 0, 0, 0, 78, 180, 182, 0, 94, 24, 0, 4, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0721_semantics :
    (Generated.hostChunk060[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[1]).mask = 48894 := by decide +kernel
  have hv : (Generated.hostChunk060[1]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 182, 0, 94, 24, 0, 4, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0721]
  rfl

theorem primitive_values_0722 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48895) = [28, 0, 0, 0, 0, 96, 276, 242, 0, 174, 40, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 112] := by
  decide +kernel

theorem primitive_host_0722_semantics :
    (Generated.hostChunk060[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[2]).mask = 48895 := by decide +kernel
  have hv : (Generated.hostChunk060[2]).primitive.toList = [28, 0, 0, 0, 0, 96, 276, 242, 0, 174, 40, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 112] := by decide +kernel
  rw [hm, hv, primitive_values_0722]
  rfl

theorem primitive_values_0723 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 49084) = [24, 0, 0, 0, 0, 62, 108, 140, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0723_semantics :
    (Generated.hostChunk060[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[3]).mask = 49084 := by decide +kernel
  have hv : (Generated.hostChunk060[3]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 140, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0723]
  rfl

theorem primitive_values_0724 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 49085) = [26, 0, 0, 0, 0, 78, 180, 184, 0, 96, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0724_semantics :
    (Generated.hostChunk060[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[4]).mask = 49085 := by decide +kernel
  have hv : (Generated.hostChunk060[4]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 184, 0, 96, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0724]
  rfl

theorem primitive_values_0725 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 49086) = [26, 0, 0, 0, 0, 76, 162, 180, 0, 78, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0725_semantics :
    (Generated.hostChunk060[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[5]).mask = 49086 := by decide +kernel
  have hv : (Generated.hostChunk060[5]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 180, 0, 78, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0725]
  rfl

theorem primitive_values_0726 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 49087) = [28, 0, 0, 0, 0, 94, 258, 238, 0, 154, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by
  decide +kernel

theorem primitive_host_0726_semantics :
    (Generated.hostChunk060[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[6]).mask = 49087 := by decide +kernel
  have hv : (Generated.hostChunk060[6]).primitive.toList = [28, 0, 0, 0, 0, 94, 258, 238, 0, 154, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by decide +kernel
  rw [hm, hv, primitive_values_0726]
  rfl

theorem primitive_values_0727 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 49150) = [28, 0, 0, 0, 0, 92, 234, 236, 0, 134, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0727_semantics :
    (Generated.hostChunk060[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[7]).mask = 49150 := by decide +kernel
  have hv : (Generated.hostChunk060[7]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 236, 0, 134, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0727]
  rfl

theorem primitive_values_0728 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 49151) = [30, 0, 0, 0, 0, 112, 354, 308, 0, 246, 40, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 184] := by
  decide +kernel

theorem primitive_host_0728_semantics :
    (Generated.hostChunk060[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[8]).mask = 49151 := by decide +kernel
  have hv : (Generated.hostChunk060[8]).primitive.toList = [30, 0, 0, 0, 0, 112, 354, 308, 0, 246, 40, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 184] := by decide +kernel
  rw [hm, hv, primitive_values_0728]
  rfl

theorem primitive_values_0729 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 58931) = [18, 0, 0, 0, 0, 36, 48, 56, 0, 32, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0729_semantics :
    (Generated.hostChunk060[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[9]).mask = 58931 := by decide +kernel
  have hv : (Generated.hostChunk060[9]).primitive.toList = [18, 0, 0, 0, 0, 36, 48, 56, 0, 32, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0729]
  rfl

theorem primitive_values_0730 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 58935) = [20, 0, 0, 0, 0, 46, 84, 80, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0730_semantics :
    (Generated.hostChunk060[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[10]).mask = 58935 := by decide +kernel
  have hv : (Generated.hostChunk060[10]).primitive.toList = [20, 0, 0, 0, 0, 46, 84, 80, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0730]
  rfl

theorem primitive_values_0731 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 58943) = [22, 0, 0, 0, 0, 58, 144, 104, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0731_semantics :
    (Generated.hostChunk060[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk060[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk060[11]).mask = 58943 := by decide +kernel
  have hv : (Generated.hostChunk060[11]).primitive.toList = [22, 0, 0, 0, 0, 58, 144, 104, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0731]
  rfl

theorem primitive_chunk_060_semantics :
    ∀ h ∈ Generated.hostChunk060.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk060.toList = [Generated.hostChunk060[0], Generated.hostChunk060[1], Generated.hostChunk060[2], Generated.hostChunk060[3], Generated.hostChunk060[4], Generated.hostChunk060[5], Generated.hostChunk060[6], Generated.hostChunk060[7], Generated.hostChunk060[8], Generated.hostChunk060[9], Generated.hostChunk060[10], Generated.hostChunk060[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0720_semantics
  · exact primitive_host_0721_semantics
  · exact primitive_host_0722_semantics
  · exact primitive_host_0723_semantics
  · exact primitive_host_0724_semantics
  · exact primitive_host_0725_semantics
  · exact primitive_host_0726_semantics
  · exact primitive_host_0727_semantics
  · exact primitive_host_0728_semantics
  · exact primitive_host_0729_semantics
  · exact primitive_host_0730_semantics
  · exact primitive_host_0731_semantics

end InducedPentagons.Paper

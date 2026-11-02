import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData013
import InducedPentagonsPaper.Generated.PrimitiveRows005

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0156 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2927) = [18, 0, 0, 0, 0, 42, 90, 60, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0156_semantics :
    (Generated.hostChunk013[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[0]).mask = 2927 := by decide +kernel
  have hv : (Generated.hostChunk013[0]).primitive.toList = [18, 0, 0, 0, 0, 42, 90, 60, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0156]
  rfl

theorem primitive_values_0157 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2936) = [14, 0, 0, 0, 0, 18, 12, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0157_semantics :
    (Generated.hostChunk013[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[1]).mask = 2936 := by decide +kernel
  have hv : (Generated.hostChunk013[1]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0157]
  rfl

theorem primitive_values_0158 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2937) = [16, 0, 0, 0, 0, 30, 48, 36, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0158_semantics :
    (Generated.hostChunk013[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[2]).mask = 2937 := by decide +kernel
  have hv : (Generated.hostChunk013[2]).primitive.toList = [16, 0, 0, 0, 0, 30, 48, 36, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0158]
  rfl

theorem primitive_values_0159 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2938) = [16, 0, 0, 0, 0, 28, 36, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0159_semantics :
    (Generated.hostChunk013[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[3]).mask = 2938 := by decide +kernel
  have hv : (Generated.hostChunk013[3]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0159]
  rfl

theorem primitive_values_0160 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2939) = [18, 0, 0, 0, 0, 42, 90, 62, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0160_semantics :
    (Generated.hostChunk013[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[4]).mask = 2939 := by decide +kernel
  have hv : (Generated.hostChunk013[4]).primitive.toList = [18, 0, 0, 0, 0, 42, 90, 62, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0160]
  rfl

theorem primitive_values_0161 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2940) = [16, 20, 12, 8, 0, 26, 30, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0161_semantics :
    (Generated.hostChunk013[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[5]).mask = 2940 := by decide +kernel
  have hv : (Generated.hostChunk013[5]).primitive.toList = [16, 20, 12, 8, 0, 26, 30, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0161]
  rfl

theorem primitive_values_0162 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2941) = [18, 0, 0, 0, 0, 40, 84, 56, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0162_semantics :
    (Generated.hostChunk013[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[6]).mask = 2941 := by decide +kernel
  have hv : (Generated.hostChunk013[6]).primitive.toList = [18, 0, 0, 0, 0, 40, 84, 56, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0162]
  rfl

theorem primitive_values_0163 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2942) = [18, 0, 0, 0, 0, 38, 72, 54, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0163_semantics :
    (Generated.hostChunk013[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[7]).mask = 2942 := by decide +kernel
  have hv : (Generated.hostChunk013[7]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 54, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0163]
  rfl

theorem primitive_values_0164 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2943) = [20, 0, 0, 0, 0, 54, 150, 84, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0164_semantics :
    (Generated.hostChunk013[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[8]).mask = 2943 := by decide +kernel
  have hv : (Generated.hostChunk013[8]).primitive.toList = [20, 0, 0, 0, 0, 54, 150, 84, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0164]
  rfl

theorem primitive_values_0165 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3038) = [18, 0, 0, 0, 0, 40, 60, 68, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0165_semantics :
    (Generated.hostChunk013[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[9]).mask = 3038 := by decide +kernel
  have hv : (Generated.hostChunk013[9]).primitive.toList = [18, 0, 0, 0, 0, 40, 60, 68, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0165]
  rfl

theorem primitive_values_0166 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3039) = [20, 0, 0, 0, 0, 56, 132, 100, 0, 72, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0166_semantics :
    (Generated.hostChunk013[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[10]).mask = 3039 := by decide +kernel
  have hv : (Generated.hostChunk013[10]).primitive.toList = [20, 0, 0, 0, 0, 56, 132, 100, 0, 72, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0166]
  rfl

theorem primitive_values_0167 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3054) = [18, 0, 0, 0, 0, 38, 60, 56, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0167_semantics :
    (Generated.hostChunk013[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk013[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk013[11]).mask = 3054 := by decide +kernel
  have hv : (Generated.hostChunk013[11]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 56, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0167]
  rfl

theorem primitive_chunk_013_semantics :
    ∀ h ∈ Generated.hostChunk013.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk013.toList = [Generated.hostChunk013[0], Generated.hostChunk013[1], Generated.hostChunk013[2], Generated.hostChunk013[3], Generated.hostChunk013[4], Generated.hostChunk013[5], Generated.hostChunk013[6], Generated.hostChunk013[7], Generated.hostChunk013[8], Generated.hostChunk013[9], Generated.hostChunk013[10], Generated.hostChunk013[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0156_semantics
  · exact primitive_host_0157_semantics
  · exact primitive_host_0158_semantics
  · exact primitive_host_0159_semantics
  · exact primitive_host_0160_semantics
  · exact primitive_host_0161_semantics
  · exact primitive_host_0162_semantics
  · exact primitive_host_0163_semantics
  · exact primitive_host_0164_semantics
  · exact primitive_host_0165_semantics
  · exact primitive_host_0166_semantics
  · exact primitive_host_0167_semantics

end InducedPentagons.Paper

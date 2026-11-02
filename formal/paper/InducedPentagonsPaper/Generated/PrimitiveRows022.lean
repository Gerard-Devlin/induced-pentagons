import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData022
import InducedPentagonsPaper.Generated.PrimitiveRows014

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0264 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7089) = [16, 0, 0, 0, 0, 26, 30, 32, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0264_semantics :
    (Generated.hostChunk022[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[0]).mask = 7089 := by decide +kernel
  have hv : (Generated.hostChunk022[0]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 32, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0264]
  rfl

theorem primitive_values_0265 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7090) = [16, 20, 12, 0, 0, 24, 18, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0265_semantics :
    (Generated.hostChunk022[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[1]).mask = 7090 := by decide +kernel
  have hv : (Generated.hostChunk022[1]).primitive.toList = [16, 20, 12, 0, 0, 24, 18, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0265]
  rfl

theorem primitive_values_0266 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7091) = [18, 0, 0, 0, 0, 36, 54, 56, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0266_semantics :
    (Generated.hostChunk022[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[2]).mask = 7091 := by decide +kernel
  have hv : (Generated.hostChunk022[2]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 56, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0266]
  rfl

theorem primitive_values_0267 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7092) = [16, 0, 0, 0, 0, 24, 18, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0267_semantics :
    (Generated.hostChunk022[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[3]).mask = 7092 := by decide +kernel
  have hv : (Generated.hostChunk022[3]).primitive.toList = [16, 0, 0, 0, 0, 24, 18, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0267]
  rfl

theorem primitive_values_0268 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7093) = [18, 0, 0, 0, 0, 36, 54, 54, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0268_semantics :
    (Generated.hostChunk022[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[4]).mask = 7093 := by decide +kernel
  have hv : (Generated.hostChunk022[4]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 54, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0268]
  rfl

theorem primitive_values_0269 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7094) = [18, 10, 8, 4, 0, 34, 42, 52, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0269_semantics :
    (Generated.hostChunk022[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[5]).mask = 7094 := by decide +kernel
  have hv : (Generated.hostChunk022[5]).primitive.toList = [18, 10, 8, 4, 0, 34, 42, 52, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0269]
  rfl

theorem primitive_values_0270 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7095) = [20, 0, 0, 0, 0, 48, 96, 82, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0270_semantics :
    (Generated.hostChunk022[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[6]).mask = 7095 := by decide +kernel
  have hv : (Generated.hostChunk022[6]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 82, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0270]
  rfl

theorem primitive_values_0271 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7100) = [18, 0, 0, 0, 0, 34, 42, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0271_semantics :
    (Generated.hostChunk022[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[7]).mask = 7100 := by decide +kernel
  have hv : (Generated.hostChunk022[7]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0271]
  rfl

theorem primitive_values_0272 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7101) = [20, 0, 0, 0, 0, 48, 96, 84, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0272_semantics :
    (Generated.hostChunk022[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[8]).mask = 7101 := by decide +kernel
  have hv : (Generated.hostChunk022[8]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 84, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0272]
  rfl

theorem primitive_values_0273 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7102) = [20, 0, 0, 0, 0, 46, 84, 80, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0273_semantics :
    (Generated.hostChunk022[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[9]).mask = 7102 := by decide +kernel
  have hv : (Generated.hostChunk022[9]).primitive.toList = [20, 0, 0, 0, 0, 46, 84, 80, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0273]
  rfl

theorem primitive_values_0274 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7103) = [22, 0, 0, 0, 0, 62, 162, 116, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0274_semantics :
    (Generated.hostChunk022[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[10]).mask = 7103 := by decide +kernel
  have hv : (Generated.hostChunk022[10]).primitive.toList = [22, 0, 0, 0, 0, 62, 162, 116, 0, 64, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0274]
  rfl

theorem primitive_values_0275 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7134) = [20, 0, 0, 0, 0, 50, 84, 96, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0275_semantics :
    (Generated.hostChunk022[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk022[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk022[11]).mask = 7134 := by decide +kernel
  have hv : (Generated.hostChunk022[11]).primitive.toList = [20, 0, 0, 0, 0, 50, 84, 96, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0275]
  rfl

theorem primitive_chunk_022_semantics :
    ∀ h ∈ Generated.hostChunk022.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk022.toList = [Generated.hostChunk022[0], Generated.hostChunk022[1], Generated.hostChunk022[2], Generated.hostChunk022[3], Generated.hostChunk022[4], Generated.hostChunk022[5], Generated.hostChunk022[6], Generated.hostChunk022[7], Generated.hostChunk022[8], Generated.hostChunk022[9], Generated.hostChunk022[10], Generated.hostChunk022[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0264_semantics
  · exact primitive_host_0265_semantics
  · exact primitive_host_0266_semantics
  · exact primitive_host_0267_semantics
  · exact primitive_host_0268_semantics
  · exact primitive_host_0269_semantics
  · exact primitive_host_0270_semantics
  · exact primitive_host_0271_semantics
  · exact primitive_host_0272_semantics
  · exact primitive_host_0273_semantics
  · exact primitive_host_0274_semantics
  · exact primitive_host_0275_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData015
import InducedPentagonsPaper.Generated.PrimitiveRows007

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0180 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3903) = [20, 0, 0, 0, 0, 52, 144, 76, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0180_semantics :
    (Generated.hostChunk015[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[0]).mask = 3903 := by decide +kernel
  have hv : (Generated.hostChunk015[0]).primitive.toList = [20, 0, 0, 0, 0, 52, 144, 76, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0180]
  rfl

theorem primitive_values_0181 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3962) = [18, 0, 0, 0, 0, 36, 54, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0181_semantics :
    (Generated.hostChunk015[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[1]).mask = 3962 := by decide +kernel
  have hv : (Generated.hostChunk015[1]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0181]
  rfl

theorem primitive_values_0182 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3963) = [20, 0, 0, 0, 0, 52, 126, 88, 0, 50, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0182_semantics :
    (Generated.hostChunk015[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[2]).mask = 3963 := by decide +kernel
  have hv : (Generated.hostChunk015[2]).primitive.toList = [20, 0, 0, 0, 0, 52, 126, 88, 0, 50, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0182]
  rfl

theorem primitive_values_0183 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3964) = [18, 30, 24, 24, 0, 34, 48, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0183_semantics :
    (Generated.hostChunk015[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[3]).mask = 3964 := by decide +kernel
  have hv : (Generated.hostChunk015[3]).primitive.toList = [18, 30, 24, 24, 0, 34, 48, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0183]
  rfl

theorem primitive_values_0184 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3965) = [20, 0, 0, 0, 0, 50, 120, 80, 0, 36, 12, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0184_semantics :
    (Generated.hostChunk015[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[4]).mask = 3965 := by decide +kernel
  have hv : (Generated.hostChunk015[4]).primitive.toList = [20, 0, 0, 0, 0, 50, 120, 80, 0, 36, 12, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0184]
  rfl

theorem primitive_values_0185 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3966) = [20, 0, 0, 0, 0, 46, 90, 76, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0185_semantics :
    (Generated.hostChunk015[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[5]).mask = 3966 := by decide +kernel
  have hv : (Generated.hostChunk015[5]).primitive.toList = [20, 0, 0, 0, 0, 46, 90, 76, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0185]
  rfl

theorem primitive_values_0186 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3967) = [22, 0, 0, 0, 0, 64, 186, 114, 0, 68, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0186_semantics :
    (Generated.hostChunk015[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[6]).mask = 3967 := by decide +kernel
  have hv : (Generated.hostChunk015[6]).primitive.toList = [22, 0, 0, 0, 0, 64, 186, 114, 0, 68, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0186]
  rfl

theorem primitive_values_0187 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 4094) = [22, 0, 0, 0, 0, 58, 132, 108, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0187_semantics :
    (Generated.hostChunk015[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[7]).mask = 4094 := by decide +kernel
  have hv : (Generated.hostChunk015[7]).primitive.toList = [22, 0, 0, 0, 0, 58, 132, 108, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0187]
  rfl

theorem primitive_values_0188 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 4095) = [24, 0, 0, 0, 0, 78, 252, 156, 0, 108, 36, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0188_semantics :
    (Generated.hostChunk015[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[8]).mask = 4095 := by decide +kernel
  have hv : (Generated.hostChunk015[8]).primitive.toList = [24, 0, 0, 0, 0, 78, 252, 156, 0, 108, 36, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0188]
  rfl

theorem primitive_values_0189 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6543) = [16, 0, 0, 0, 0, 36, 48, 56, 0, 32, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0189_semantics :
    (Generated.hostChunk015[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[9]).mask = 6543 := by decide +kernel
  have hv : (Generated.hostChunk015[9]).primitive.toList = [16, 0, 0, 0, 0, 36, 48, 56, 0, 32, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0189]
  rfl

theorem primitive_values_0190 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6549) = [14, 0, 0, 0, 0, 22, 18, 28, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0190_semantics :
    (Generated.hostChunk015[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[10]).mask = 6549 := by decide +kernel
  have hv : (Generated.hostChunk015[10]).primitive.toList = [14, 0, 0, 0, 0, 22, 18, 28, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0190]
  rfl

theorem primitive_values_0191 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6551) = [16, 0, 0, 0, 0, 32, 42, 48, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0191_semantics :
    (Generated.hostChunk015[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk015[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk015[11]).mask = 6551 := by decide +kernel
  have hv : (Generated.hostChunk015[11]).primitive.toList = [16, 0, 0, 0, 0, 32, 42, 48, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0191]
  rfl

theorem primitive_chunk_015_semantics :
    ∀ h ∈ Generated.hostChunk015.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk015.toList = [Generated.hostChunk015[0], Generated.hostChunk015[1], Generated.hostChunk015[2], Generated.hostChunk015[3], Generated.hostChunk015[4], Generated.hostChunk015[5], Generated.hostChunk015[6], Generated.hostChunk015[7], Generated.hostChunk015[8], Generated.hostChunk015[9], Generated.hostChunk015[10], Generated.hostChunk015[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0180_semantics
  · exact primitive_host_0181_semantics
  · exact primitive_host_0182_semantics
  · exact primitive_host_0183_semantics
  · exact primitive_host_0184_semantics
  · exact primitive_host_0185_semantics
  · exact primitive_host_0186_semantics
  · exact primitive_host_0187_semantics
  · exact primitive_host_0188_semantics
  · exact primitive_host_0189_semantics
  · exact primitive_host_0190_semantics
  · exact primitive_host_0191_semantics

end InducedPentagons.Paper

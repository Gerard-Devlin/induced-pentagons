import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData020
import InducedPentagonsPaper.Generated.PrimitiveRows012

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0240 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6877) = [18, 0, 0, 0, 0, 40, 60, 66, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0240_semantics :
    (Generated.hostChunk020[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[0]).mask = 6877 := by decide +kernel
  have hv : (Generated.hostChunk020[0]).primitive.toList = [18, 0, 0, 0, 0, 40, 60, 66, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0240]
  rfl

theorem primitive_values_0241 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6879) = [20, 0, 0, 0, 0, 54, 114, 98, 0, 68, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0241_semantics :
    (Generated.hostChunk020[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[1]).mask = 6879 := by decide +kernel
  have hv : (Generated.hostChunk020[1]).primitive.toList = [20, 0, 0, 0, 0, 54, 114, 98, 0, 68, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0241]
  rfl

theorem primitive_values_0242 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6887) = [18, 0, 0, 0, 0, 42, 78, 66, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0242_semantics :
    (Generated.hostChunk020[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[2]).mask = 6887 := by decide +kernel
  have hv : (Generated.hostChunk020[2]).primitive.toList = [18, 0, 0, 0, 0, 42, 78, 66, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0242]
  rfl

theorem primitive_values_0243 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6890) = [16, 0, 0, 0, 0, 28, 36, 32, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0243_semantics :
    (Generated.hostChunk020[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[3]).mask = 6890 := by decide +kernel
  have hv : (Generated.hostChunk020[3]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 32, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0243]
  rfl

theorem primitive_values_0244 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6891) = [18, 0, 0, 0, 0, 40, 72, 60, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0244_semantics :
    (Generated.hostChunk020[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[4]).mask = 6891 := by decide +kernel
  have hv : (Generated.hostChunk020[4]).primitive.toList = [18, 0, 0, 0, 0, 40, 72, 60, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0244]
  rfl

theorem primitive_values_0245 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6892) = [16, 0, 0, 0, 0, 26, 24, 34, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0245_semantics :
    (Generated.hostChunk020[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[5]).mask = 6892 := by decide +kernel
  have hv : (Generated.hostChunk020[5]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 34, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0245]
  rfl

theorem primitive_values_0246 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6893) = [18, 0, 0, 0, 0, 38, 60, 60, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0246_semantics :
    (Generated.hostChunk020[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[6]).mask = 6893 := by decide +kernel
  have hv : (Generated.hostChunk020[6]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 60, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0246]
  rfl

theorem primitive_values_0247 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6894) = [18, 0, 0, 0, 0, 38, 60, 56, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0247_semantics :
    (Generated.hostChunk020[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[7]).mask = 6894 := by decide +kernel
  have hv : (Generated.hostChunk020[7]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 56, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0247]
  rfl

theorem primitive_values_0248 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6895) = [20, 0, 0, 0, 0, 52, 114, 90, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0248_semantics :
    (Generated.hostChunk020[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[8]).mask = 6895 := by decide +kernel
  have hv : (Generated.hostChunk020[8]).primitive.toList = [20, 0, 0, 0, 0, 52, 114, 90, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0248]
  rfl

theorem primitive_values_0249 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6904) = [16, 10, 6, 0, 0, 24, 18, 26, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0249_semantics :
    (Generated.hostChunk020[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[9]).mask = 6904 := by decide +kernel
  have hv : (Generated.hostChunk020[9]).primitive.toList = [16, 10, 6, 0, 0, 24, 18, 26, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0249]
  rfl

theorem primitive_values_0250 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6905) = [18, 0, 0, 0, 0, 36, 54, 50, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0250_semantics :
    (Generated.hostChunk020[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[10]).mask = 6905 := by decide +kernel
  have hv : (Generated.hostChunk020[10]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 50, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0250]
  rfl

theorem primitive_values_0251 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6907) = [20, 0, 0, 0, 0, 50, 108, 82, 0, 42, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0251_semantics :
    (Generated.hostChunk020[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk020[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk020[11]).mask = 6907 := by decide +kernel
  have hv : (Generated.hostChunk020[11]).primitive.toList = [20, 0, 0, 0, 0, 50, 108, 82, 0, 42, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0251]
  rfl

theorem primitive_chunk_020_semantics :
    ∀ h ∈ Generated.hostChunk020.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk020.toList = [Generated.hostChunk020[0], Generated.hostChunk020[1], Generated.hostChunk020[2], Generated.hostChunk020[3], Generated.hostChunk020[4], Generated.hostChunk020[5], Generated.hostChunk020[6], Generated.hostChunk020[7], Generated.hostChunk020[8], Generated.hostChunk020[9], Generated.hostChunk020[10], Generated.hostChunk020[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0240_semantics
  · exact primitive_host_0241_semantics
  · exact primitive_host_0242_semantics
  · exact primitive_host_0243_semantics
  · exact primitive_host_0244_semantics
  · exact primitive_host_0245_semantics
  · exact primitive_host_0246_semantics
  · exact primitive_host_0247_semantics
  · exact primitive_host_0248_semantics
  · exact primitive_host_0249_semantics
  · exact primitive_host_0250_semantics
  · exact primitive_host_0251_semantics

end InducedPentagons.Paper

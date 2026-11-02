import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData018
import InducedPentagonsPaper.Generated.PrimitiveRows010

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0216 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6809) = [14, 10, 4, 0, 0, 20, 12, 22, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0216_semantics :
    (Generated.hostChunk018[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[0]).mask = 6809 := by decide +kernel
  have hv : (Generated.hostChunk018[0]).primitive.toList = [14, 10, 4, 0, 0, 20, 12, 22, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0216]
  rfl

theorem primitive_values_0217 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6811) = [16, 0, 0, 0, 0, 30, 36, 40, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0217_semantics :
    (Generated.hostChunk018[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[1]).mask = 6811 := by decide +kernel
  have hv : (Generated.hostChunk018[1]).primitive.toList = [16, 0, 0, 0, 0, 30, 36, 40, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0217]
  rfl

theorem primitive_values_0218 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6812) = [14, 0, 0, 0, 0, 20, 12, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0218_semantics :
    (Generated.hostChunk018[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[2]).mask = 6812 := by decide +kernel
  have hv : (Generated.hostChunk018[2]).primitive.toList = [14, 0, 0, 0, 0, 20, 12, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0218]
  rfl

theorem primitive_values_0219 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6813) = [16, 0, 0, 0, 0, 30, 36, 42, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0219_semantics :
    (Generated.hostChunk018[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[3]).mask = 6813 := by decide +kernel
  have hv : (Generated.hostChunk018[3]).primitive.toList = [16, 0, 0, 0, 0, 30, 36, 42, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0219]
  rfl

theorem primitive_values_0220 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6815) = [18, 0, 0, 0, 0, 42, 78, 64, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0220_semantics :
    (Generated.hostChunk018[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[4]).mask = 6815 := by decide +kernel
  have hv : (Generated.hostChunk018[4]).primitive.toList = [18, 0, 0, 0, 0, 42, 78, 64, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0220]
  rfl

theorem primitive_values_0221 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6820) = [12, 0, 0, 0, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0221_semantics :
    (Generated.hostChunk018[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[5]).mask = 6820 := by decide +kernel
  have hv : (Generated.hostChunk018[5]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0221]
  rfl

theorem primitive_values_0222 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6821) = [14, 0, 0, 0, 0, 20, 18, 22, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0222_semantics :
    (Generated.hostChunk018[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[6]).mask = 6821 := by decide +kernel
  have hv : (Generated.hostChunk018[6]).primitive.toList = [14, 0, 0, 0, 0, 20, 18, 22, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0222]
  rfl

theorem primitive_values_0223 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6823) = [16, 0, 0, 0, 0, 30, 42, 40, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0223_semantics :
    (Generated.hostChunk018[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[7]).mask = 6823 := by decide +kernel
  have hv : (Generated.hostChunk018[7]).primitive.toList = [16, 0, 0, 0, 0, 30, 42, 40, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0223]
  rfl

theorem primitive_values_0224 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6824) = [12, 0, 0, 0, 0, 10, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0224_semantics :
    (Generated.hostChunk018[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[8]).mask = 6824 := by decide +kernel
  have hv : (Generated.hostChunk018[8]).primitive.toList = [12, 0, 0, 0, 0, 10, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0224]
  rfl

theorem primitive_values_0225 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6825) = [14, 10, 4, 0, 0, 18, 12, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0225_semantics :
    (Generated.hostChunk018[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[9]).mask = 6825 := by decide +kernel
  have hv : (Generated.hostChunk018[9]).primitive.toList = [14, 10, 4, 0, 0, 18, 12, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0225]
  rfl

theorem primitive_values_0226 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6826) = [14, 0, 0, 0, 0, 18, 12, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0226_semantics :
    (Generated.hostChunk018[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[10]).mask = 6826 := by decide +kernel
  have hv : (Generated.hostChunk018[10]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0226]
  rfl

theorem primitive_values_0227 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6827) = [16, 0, 0, 0, 0, 28, 36, 36, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0227_semantics :
    (Generated.hostChunk018[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk018[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk018[11]).mask = 6827 := by decide +kernel
  have hv : (Generated.hostChunk018[11]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 36, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0227]
  rfl

theorem primitive_chunk_018_semantics :
    ∀ h ∈ Generated.hostChunk018.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk018.toList = [Generated.hostChunk018[0], Generated.hostChunk018[1], Generated.hostChunk018[2], Generated.hostChunk018[3], Generated.hostChunk018[4], Generated.hostChunk018[5], Generated.hostChunk018[6], Generated.hostChunk018[7], Generated.hostChunk018[8], Generated.hostChunk018[9], Generated.hostChunk018[10], Generated.hostChunk018[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0216_semantics
  · exact primitive_host_0217_semantics
  · exact primitive_host_0218_semantics
  · exact primitive_host_0219_semantics
  · exact primitive_host_0220_semantics
  · exact primitive_host_0221_semantics
  · exact primitive_host_0222_semantics
  · exact primitive_host_0223_semantics
  · exact primitive_host_0224_semantics
  · exact primitive_host_0225_semantics
  · exact primitive_host_0226_semantics
  · exact primitive_host_0227_semantics

end InducedPentagons.Paper

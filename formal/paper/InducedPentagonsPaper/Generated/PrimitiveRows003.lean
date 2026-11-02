import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData003

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0036 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 254) = [14, 0, 0, 0, 0, 26, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0036_semantics :
    (Generated.hostChunk003[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[0]).mask = 254 := by decide +kernel
  have hv : (Generated.hostChunk003[0]).primitive.toList = [14, 0, 0, 0, 0, 26, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0036]
  rfl

theorem primitive_values_0037 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 255) = [16, 0, 0, 0, 0, 40, 126, 36, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0037_semantics :
    (Generated.hostChunk003[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[1]).mask = 255 := by decide +kernel
  have hv : (Generated.hostChunk003[1]).primitive.toList = [16, 0, 0, 0, 0, 40, 126, 36, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0037]
  rfl

theorem primitive_values_0038 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 462) = [12, 0, 0, 0, 0, 18, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0038_semantics :
    (Generated.hostChunk003[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[2]).mask = 462 := by decide +kernel
  have hv : (Generated.hostChunk003[2]).primitive.toList = [12, 0, 0, 0, 0, 18, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0038]
  rfl

theorem primitive_values_0039 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 463) = [14, 0, 0, 0, 0, 30, 48, 36, 0, 24, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0039_semantics :
    (Generated.hostChunk003[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[3]).mask = 463 := by decide +kernel
  have hv : (Generated.hostChunk003[3]).primitive.toList = [14, 0, 0, 0, 0, 30, 48, 36, 0, 24, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0039]
  rfl

theorem primitive_values_0040 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 470) = [12, 0, 0, 0, 0, 16, 12, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0040_semantics :
    (Generated.hostChunk003[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[4]).mask = 470 := by decide +kernel
  have hv : (Generated.hostChunk003[4]).primitive.toList = [12, 0, 0, 0, 0, 16, 12, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0040]
  rfl

theorem primitive_values_0041 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 471) = [14, 0, 0, 0, 0, 28, 48, 30, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0041_semantics :
    (Generated.hostChunk003[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[5]).mask = 471 := by decide +kernel
  have hv : (Generated.hostChunk003[5]).primitive.toList = [14, 0, 0, 0, 0, 28, 48, 30, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0041]
  rfl

theorem primitive_values_0042 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 478) = [14, 0, 0, 0, 0, 24, 30, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0042_semantics :
    (Generated.hostChunk003[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[6]).mask = 478 := by decide +kernel
  have hv : (Generated.hostChunk003[6]).primitive.toList = [14, 0, 0, 0, 0, 24, 30, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0042]
  rfl

theorem primitive_values_0043 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 479) = [16, 0, 0, 0, 0, 38, 84, 48, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0043_semantics :
    (Generated.hostChunk003[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[7]).mask = 479 := by decide +kernel
  have hv : (Generated.hostChunk003[7]).primitive.toList = [16, 0, 0, 0, 0, 38, 84, 48, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0043]
  rfl

theorem primitive_values_0044 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 498) = [12, 0, 0, 0, 0, 14, 12, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0044_semantics :
    (Generated.hostChunk003[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[8]).mask = 498 := by decide +kernel
  have hv : (Generated.hostChunk003[8]).primitive.toList = [12, 0, 0, 0, 0, 14, 12, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0044]
  rfl

theorem primitive_values_0045 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 499) = [14, 0, 0, 0, 0, 26, 48, 24, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0045_semantics :
    (Generated.hostChunk003[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[9]).mask = 499 := by decide +kernel
  have hv : (Generated.hostChunk003[9]).primitive.toList = [14, 0, 0, 0, 0, 26, 48, 24, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0045]
  rfl

theorem primitive_values_0046 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 502) = [14, 0, 0, 0, 0, 22, 30, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0046_semantics :
    (Generated.hostChunk003[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[10]).mask = 502 := by decide +kernel
  have hv : (Generated.hostChunk003[10]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0046]
  rfl

theorem primitive_values_0047 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 503) = [16, 0, 0, 0, 0, 36, 84, 40, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0047_semantics :
    (Generated.hostChunk003[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk003[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk003[11]).mask = 503 := by decide +kernel
  have hv : (Generated.hostChunk003[11]).primitive.toList = [16, 0, 0, 0, 0, 36, 84, 40, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0047]
  rfl

theorem primitive_chunk_003_semantics :
    ∀ h ∈ Generated.hostChunk003.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk003.toList = [Generated.hostChunk003[0], Generated.hostChunk003[1], Generated.hostChunk003[2], Generated.hostChunk003[3], Generated.hostChunk003[4], Generated.hostChunk003[5], Generated.hostChunk003[6], Generated.hostChunk003[7], Generated.hostChunk003[8], Generated.hostChunk003[9], Generated.hostChunk003[10], Generated.hostChunk003[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0036_semantics
  · exact primitive_host_0037_semantics
  · exact primitive_host_0038_semantics
  · exact primitive_host_0039_semantics
  · exact primitive_host_0040_semantics
  · exact primitive_host_0041_semantics
  · exact primitive_host_0042_semantics
  · exact primitive_host_0043_semantics
  · exact primitive_host_0044_semantics
  · exact primitive_host_0045_semantics
  · exact primitive_host_0046_semantics
  · exact primitive_host_0047_semantics

end InducedPentagons.Paper

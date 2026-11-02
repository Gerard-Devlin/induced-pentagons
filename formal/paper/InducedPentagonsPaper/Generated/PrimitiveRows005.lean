import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData005

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0060 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2249) = [10, 0, 0, 0, 0, 12, 6, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0060_semantics :
    (Generated.hostChunk005[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[0]).mask = 2249 := by decide +kernel
  have hv : (Generated.hostChunk005[0]).primitive.toList = [10, 0, 0, 0, 0, 12, 6, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0060]
  rfl

theorem primitive_values_0061 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2251) = [12, 0, 0, 0, 0, 20, 18, 20, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0061_semantics :
    (Generated.hostChunk005[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[1]).mask = 2251 := by decide +kernel
  have hv : (Generated.hostChunk005[1]).primitive.toList = [12, 0, 0, 0, 0, 20, 18, 20, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0061]
  rfl

theorem primitive_values_0062 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2255) = [14, 0, 0, 0, 0, 30, 42, 36, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0062_semantics :
    (Generated.hostChunk005[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[2]).mask = 2255 := by decide +kernel
  have hv : (Generated.hostChunk005[2]).primitive.toList = [14, 0, 0, 0, 0, 30, 42, 36, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0062]
  rfl

theorem primitive_values_0063 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2264) = [10, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0063_semantics :
    (Generated.hostChunk005[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[3]).mask = 2264 := by decide +kernel
  have hv : (Generated.hostChunk005[3]).primitive.toList = [10, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0063]
  rfl

theorem primitive_values_0064 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2265) = [12, 0, 0, 0, 0, 16, 12, 12, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0064_semantics :
    (Generated.hostChunk005[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[4]).mask = 2265 := by decide +kernel
  have hv : (Generated.hostChunk005[4]).primitive.toList = [12, 0, 0, 0, 0, 16, 12, 12, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0064]
  rfl

theorem primitive_values_0065 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2267) = [14, 0, 0, 0, 0, 26, 36, 28, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0065_semantics :
    (Generated.hostChunk005[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[5]).mask = 2267 := by decide +kernel
  have hv : (Generated.hostChunk005[5]).primitive.toList = [14, 0, 0, 0, 0, 26, 36, 28, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0065]
  rfl

theorem primitive_values_0066 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2271) = [16, 0, 0, 0, 0, 38, 78, 48, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0066_semantics :
    (Generated.hostChunk005[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[6]).mask = 2271 := by decide +kernel
  have hv : (Generated.hostChunk005[6]).primitive.toList = [16, 0, 0, 0, 0, 38, 78, 48, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0066]
  rfl

theorem primitive_values_0067 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2296) = [12, 0, 0, 0, 0, 12, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0067_semantics :
    (Generated.hostChunk005[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[7]).mask = 2296 := by decide +kernel
  have hv : (Generated.hostChunk005[7]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0067]
  rfl

theorem primitive_values_0068 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2297) = [14, 0, 0, 0, 0, 22, 30, 16, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0068_semantics :
    (Generated.hostChunk005[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[8]).mask = 2297 := by decide +kernel
  have hv : (Generated.hostChunk005[8]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 16, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0068]
  rfl

theorem primitive_values_0069 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2299) = [16, 0, 0, 0, 0, 34, 72, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0069_semantics :
    (Generated.hostChunk005[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[9]).mask = 2299 := by decide +kernel
  have hv : (Generated.hostChunk005[9]).primitive.toList = [16, 0, 0, 0, 0, 34, 72, 36, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0069]
  rfl

theorem primitive_values_0070 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2303) = [18, 0, 0, 0, 0, 48, 138, 60, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0070_semantics :
    (Generated.hostChunk005[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[10]).mask = 2303 := by decide +kernel
  have hv : (Generated.hostChunk005[10]).primitive.toList = [18, 0, 0, 0, 0, 48, 138, 60, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0070]
  rfl

theorem primitive_values_0071 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2319) = [12, 0, 0, 0, 0, 20, 24, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0071_semantics :
    (Generated.hostChunk005[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk005[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk005[11]).mask = 2319 := by decide +kernel
  have hv : (Generated.hostChunk005[11]).primitive.toList = [12, 0, 0, 0, 0, 20, 24, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0071]
  rfl

theorem primitive_chunk_005_semantics :
    ∀ h ∈ Generated.hostChunk005.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk005.toList = [Generated.hostChunk005[0], Generated.hostChunk005[1], Generated.hostChunk005[2], Generated.hostChunk005[3], Generated.hostChunk005[4], Generated.hostChunk005[5], Generated.hostChunk005[6], Generated.hostChunk005[7], Generated.hostChunk005[8], Generated.hostChunk005[9], Generated.hostChunk005[10], Generated.hostChunk005[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0060_semantics
  · exact primitive_host_0061_semantics
  · exact primitive_host_0062_semantics
  · exact primitive_host_0063_semantics
  · exact primitive_host_0064_semantics
  · exact primitive_host_0065_semantics
  · exact primitive_host_0066_semantics
  · exact primitive_host_0067_semantics
  · exact primitive_host_0068_semantics
  · exact primitive_host_0069_semantics
  · exact primitive_host_0070_semantics
  · exact primitive_host_0071_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData006

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0072 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2320) = [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0072_semantics :
    (Generated.hostChunk006[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[0]).mask = 2320 := by decide +kernel
  have hv : (Generated.hostChunk006[0]).primitive.toList = [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0072]
  rfl

theorem primitive_values_0073 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2321) = [8, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0073_semantics :
    (Generated.hostChunk006[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[1]).mask = 2321 := by decide +kernel
  have hv : (Generated.hostChunk006[1]).primitive.toList = [8, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0073]
  rfl

theorem primitive_values_0074 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2323) = [10, 0, 0, 0, 0, 10, 6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0074_semantics :
    (Generated.hostChunk006[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[2]).mask = 2323 := by decide +kernel
  have hv : (Generated.hostChunk006[2]).primitive.toList = [10, 0, 0, 0, 0, 10, 6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0074]
  rfl

theorem primitive_values_0075 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2326) = [10, 0, 0, 0, 0, 10, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0075_semantics :
    (Generated.hostChunk006[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[3]).mask = 2326 := by decide +kernel
  have hv : (Generated.hostChunk006[3]).primitive.toList = [10, 0, 0, 0, 0, 10, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0075]
  rfl

theorem primitive_values_0076 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2327) = [12, 0, 0, 0, 0, 18, 24, 14, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0076_semantics :
    (Generated.hostChunk006[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[4]).mask = 2327 := by decide +kernel
  have hv : (Generated.hostChunk006[4]).primitive.toList = [12, 0, 0, 0, 0, 18, 24, 14, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0076]
  rfl

theorem primitive_values_0077 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2335) = [14, 0, 0, 0, 0, 28, 60, 24, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0077_semantics :
    (Generated.hostChunk006[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[5]).mask = 2335 := by decide +kernel
  have hv : (Generated.hostChunk006[5]).primitive.toList = [14, 0, 0, 0, 0, 28, 60, 24, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0077]
  rfl

theorem primitive_values_0078 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2352) = [8, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0078_semantics :
    (Generated.hostChunk006[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[6]).mask = 2352 := by decide +kernel
  have hv : (Generated.hostChunk006[6]).primitive.toList = [8, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0078]
  rfl

theorem primitive_values_0079 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2353) = [10, 0, 0, 0, 0, 8, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0079_semantics :
    (Generated.hostChunk006[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[7]).mask = 2353 := by decide +kernel
  have hv : (Generated.hostChunk006[7]).primitive.toList = [10, 0, 0, 0, 0, 8, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0079]
  rfl

theorem primitive_values_0080 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2355) = [12, 0, 0, 0, 0, 16, 24, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0080_semantics :
    (Generated.hostChunk006[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[8]).mask = 2355 := by decide +kernel
  have hv : (Generated.hostChunk006[8]).primitive.toList = [12, 0, 0, 0, 0, 16, 24, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0080]
  rfl

theorem primitive_values_0081 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2358) = [12, 0, 0, 0, 0, 16, 24, 8, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0081_semantics :
    (Generated.hostChunk006[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[9]).mask = 2358 := by decide +kernel
  have hv : (Generated.hostChunk006[9]).primitive.toList = [12, 0, 0, 0, 0, 16, 24, 8, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0081]
  rfl

theorem primitive_values_0082 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2359) = [14, 0, 0, 0, 0, 26, 60, 20, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0082_semantics :
    (Generated.hostChunk006[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[10]).mask = 2359 := by decide +kernel
  have hv : (Generated.hostChunk006[10]).primitive.toList = [14, 0, 0, 0, 0, 26, 60, 20, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0082]
  rfl

theorem primitive_values_0083 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2367) = [16, 0, 0, 0, 0, 38, 120, 32, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0083_semantics :
    (Generated.hostChunk006[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk006[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk006[11]).mask = 2367 := by decide +kernel
  have hv : (Generated.hostChunk006[11]).primitive.toList = [16, 0, 0, 0, 0, 38, 120, 32, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0083]
  rfl

theorem primitive_chunk_006_semantics :
    ∀ h ∈ Generated.hostChunk006.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk006.toList = [Generated.hostChunk006[0], Generated.hostChunk006[1], Generated.hostChunk006[2], Generated.hostChunk006[3], Generated.hostChunk006[4], Generated.hostChunk006[5], Generated.hostChunk006[6], Generated.hostChunk006[7], Generated.hostChunk006[8], Generated.hostChunk006[9], Generated.hostChunk006[10], Generated.hostChunk006[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0072_semantics
  · exact primitive_host_0073_semantics
  · exact primitive_host_0074_semantics
  · exact primitive_host_0075_semantics
  · exact primitive_host_0076_semantics
  · exact primitive_host_0077_semantics
  · exact primitive_host_0078_semantics
  · exact primitive_host_0079_semantics
  · exact primitive_host_0080_semantics
  · exact primitive_host_0081_semantics
  · exact primitive_host_0082_semantics
  · exact primitive_host_0083_semantics

end InducedPentagons.Paper

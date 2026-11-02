import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData007

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0084 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2380) = [10, 10, 0, 0, 0, 10, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0084_semantics :
    (Generated.hostChunk007[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[0]).mask = 2380 := by decide +kernel
  have hv : (Generated.hostChunk007[0]).primitive.toList = [10, 10, 0, 0, 0, 10, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0084]
  rfl

theorem primitive_values_0085 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2381) = [12, 0, 0, 0, 0, 18, 12, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0085_semantics :
    (Generated.hostChunk007[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[1]).mask = 2381 := by decide +kernel
  have hv : (Generated.hostChunk007[1]).primitive.toList = [12, 0, 0, 0, 0, 18, 12, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0085]
  rfl

theorem primitive_values_0086 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2383) = [14, 0, 0, 0, 0, 28, 36, 34, 0, 20, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0086_semantics :
    (Generated.hostChunk007[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[2]).mask = 2383 := by decide +kernel
  have hv : (Generated.hostChunk007[2]).primitive.toList = [14, 0, 0, 0, 0, 28, 36, 34, 0, 20, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0086]
  rfl

theorem primitive_values_0087 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2387) = [12, 0, 0, 0, 0, 18, 18, 18, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0087_semantics :
    (Generated.hostChunk007[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[3]).mask = 2387 := by decide +kernel
  have hv : (Generated.hostChunk007[3]).primitive.toList = [12, 0, 0, 0, 0, 18, 18, 18, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0087]
  rfl

theorem primitive_values_0088 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2388) = [10, 0, 0, 0, 0, 8, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0088_semantics :
    (Generated.hostChunk007[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[4]).mask = 2388 := by decide +kernel
  have hv : (Generated.hostChunk007[4]).primitive.toList = [10, 0, 0, 0, 0, 8, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0088]
  rfl

theorem primitive_values_0089 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2389) = [12, 0, 0, 0, 0, 16, 12, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0089_semantics :
    (Generated.hostChunk007[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[5]).mask = 2389 := by decide +kernel
  have hv : (Generated.hostChunk007[5]).primitive.toList = [12, 0, 0, 0, 0, 16, 12, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0089]
  rfl

theorem primitive_values_0090 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2390) = [12, 0, 0, 0, 0, 16, 12, 14, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0090_semantics :
    (Generated.hostChunk007[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[6]).mask = 2390 := by decide +kernel
  have hv : (Generated.hostChunk007[6]).primitive.toList = [12, 0, 0, 0, 0, 16, 12, 14, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0090]
  rfl

theorem primitive_values_0091 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2391) = [14, 0, 0, 0, 0, 26, 36, 30, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0091_semantics :
    (Generated.hostChunk007[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[7]).mask = 2391 := by decide +kernel
  have hv : (Generated.hostChunk007[7]).primitive.toList = [14, 0, 0, 0, 0, 26, 36, 30, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0091]
  rfl

theorem primitive_values_0092 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2396) = [12, 10, 2, 0, 0, 14, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0092_semantics :
    (Generated.hostChunk007[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[8]).mask = 2396 := by decide +kernel
  have hv : (Generated.hostChunk007[8]).primitive.toList = [12, 10, 2, 0, 0, 14, 6, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0092]
  rfl

theorem primitive_values_0093 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2397) = [14, 0, 0, 0, 0, 24, 30, 28, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0093_semantics :
    (Generated.hostChunk007[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[9]).mask = 2397 := by decide +kernel
  have hv : (Generated.hostChunk007[9]).primitive.toList = [14, 0, 0, 0, 0, 24, 30, 28, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0093]
  rfl

theorem primitive_values_0094 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2399) = [16, 0, 0, 0, 0, 36, 72, 46, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0094_semantics :
    (Generated.hostChunk007[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[10]).mask = 2399 := by decide +kernel
  have hv : (Generated.hostChunk007[10]).primitive.toList = [16, 0, 0, 0, 0, 36, 72, 46, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0094]
  rfl

theorem primitive_values_0095 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2416) = [10, 0, 0, 0, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0095_semantics :
    (Generated.hostChunk007[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk007[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk007[11]).mask = 2416 := by decide +kernel
  have hv : (Generated.hostChunk007[11]).primitive.toList = [10, 0, 0, 0, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0095]
  rfl

theorem primitive_chunk_007_semantics :
    ∀ h ∈ Generated.hostChunk007.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk007.toList = [Generated.hostChunk007[0], Generated.hostChunk007[1], Generated.hostChunk007[2], Generated.hostChunk007[3], Generated.hostChunk007[4], Generated.hostChunk007[5], Generated.hostChunk007[6], Generated.hostChunk007[7], Generated.hostChunk007[8], Generated.hostChunk007[9], Generated.hostChunk007[10], Generated.hostChunk007[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0084_semantics
  · exact primitive_host_0085_semantics
  · exact primitive_host_0086_semantics
  · exact primitive_host_0087_semantics
  · exact primitive_host_0088_semantics
  · exact primitive_host_0089_semantics
  · exact primitive_host_0090_semantics
  · exact primitive_host_0091_semantics
  · exact primitive_host_0092_semantics
  · exact primitive_host_0093_semantics
  · exact primitive_host_0094_semantics
  · exact primitive_host_0095_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData030
import InducedPentagonsPaper.Generated.PrimitiveRows022

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0360 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39376) = [14, 0, 0, 0, 0, 24, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0360_semantics :
    (Generated.hostChunk030[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[0]).mask = 39376 := by decide +kernel
  have hv : (Generated.hostChunk030[0]).primitive.toList = [14, 0, 0, 0, 0, 24, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0360]
  rfl

theorem primitive_values_0361 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39377) = [16, 0, 0, 0, 0, 32, 42, 42, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0361_semantics :
    (Generated.hostChunk030[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[1]).mask = 39377 := by decide +kernel
  have hv : (Generated.hostChunk030[1]).primitive.toList = [16, 0, 0, 0, 0, 32, 42, 42, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0361]
  rfl

theorem primitive_values_0362 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39379) = [18, 0, 0, 0, 0, 42, 66, 68, 0, 46, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0362_semantics :
    (Generated.hostChunk030[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[2]).mask = 39379 := by decide +kernel
  have hv : (Generated.hostChunk030[2]).primitive.toList = [18, 0, 0, 0, 0, 42, 66, 68, 0, 46, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0362]
  rfl

theorem primitive_values_0363 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39383) = [20, 0, 0, 0, 0, 54, 102, 102, 0, 78, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0363_semantics :
    (Generated.hostChunk030[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[3]).mask = 39383 := by decide +kernel
  have hv : (Generated.hostChunk030[3]).primitive.toList = [20, 0, 0, 0, 0, 54, 102, 102, 0, 78, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0363]
  rfl

theorem primitive_values_0364 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39391) = [22, 0, 0, 0, 0, 68, 156, 144, 0, 132, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0364_semantics :
    (Generated.hostChunk030[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[4]).mask = 39391 := by decide +kernel
  have hv : (Generated.hostChunk030[4]).primitive.toList = [22, 0, 0, 0, 0, 68, 156, 144, 0, 132, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0364]
  rfl

theorem primitive_values_0365 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39408) = [16, 0, 0, 0, 0, 26, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0365_semantics :
    (Generated.hostChunk030[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[5]).mask = 39408 := by decide +kernel
  have hv : (Generated.hostChunk030[5]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0365]
  rfl

theorem primitive_values_0366 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39409) = [18, 0, 0, 0, 0, 36, 48, 48, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0366_semantics :
    (Generated.hostChunk030[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[6]).mask = 39409 := by decide +kernel
  have hv : (Generated.hostChunk030[6]).primitive.toList = [18, 0, 0, 0, 0, 36, 48, 48, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0366]
  rfl

theorem primitive_values_0367 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39411) = [20, 0, 0, 0, 0, 48, 84, 80, 0, 48, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0367_semantics :
    (Generated.hostChunk030[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[7]).mask = 39411 := by decide +kernel
  have hv : (Generated.hostChunk030[7]).primitive.toList = [20, 0, 0, 0, 0, 48, 84, 80, 0, 48, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0367]
  rfl

theorem primitive_values_0368 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39415) = [22, 0, 0, 0, 0, 62, 138, 120, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0368_semantics :
    (Generated.hostChunk030[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[8]).mask = 39415 := by decide +kernel
  have hv : (Generated.hostChunk030[8]).primitive.toList = [22, 0, 0, 0, 0, 62, 138, 120, 0, 84, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0368]
  rfl

theorem primitive_values_0369 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39423) = [24, 0, 0, 0, 0, 78, 216, 168, 0, 144, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0369_semantics :
    (Generated.hostChunk030[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[9]).mask = 39423 := by decide +kernel
  have hv : (Generated.hostChunk030[9]).primitive.toList = [24, 0, 0, 0, 0, 78, 216, 168, 0, 144, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0369]
  rfl

theorem primitive_values_0370 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39441) = [12, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0370_semantics :
    (Generated.hostChunk030[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[10]).mask = 39441 := by decide +kernel
  have hv : (Generated.hostChunk030[10]).primitive.toList = [12, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0370]
  rfl

theorem primitive_values_0371 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39443) = [14, 0, 0, 0, 0, 20, 12, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0371_semantics :
    (Generated.hostChunk030[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk030[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk030[11]).mask = 39443 := by decide +kernel
  have hv : (Generated.hostChunk030[11]).primitive.toList = [14, 0, 0, 0, 0, 20, 12, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0371]
  rfl

theorem primitive_chunk_030_semantics :
    ∀ h ∈ Generated.hostChunk030.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk030.toList = [Generated.hostChunk030[0], Generated.hostChunk030[1], Generated.hostChunk030[2], Generated.hostChunk030[3], Generated.hostChunk030[4], Generated.hostChunk030[5], Generated.hostChunk030[6], Generated.hostChunk030[7], Generated.hostChunk030[8], Generated.hostChunk030[9], Generated.hostChunk030[10], Generated.hostChunk030[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0360_semantics
  · exact primitive_host_0361_semantics
  · exact primitive_host_0362_semantics
  · exact primitive_host_0363_semantics
  · exact primitive_host_0364_semantics
  · exact primitive_host_0365_semantics
  · exact primitive_host_0366_semantics
  · exact primitive_host_0367_semantics
  · exact primitive_host_0368_semantics
  · exact primitive_host_0369_semantics
  · exact primitive_host_0370_semantics
  · exact primitive_host_0371_semantics

end InducedPentagons.Paper

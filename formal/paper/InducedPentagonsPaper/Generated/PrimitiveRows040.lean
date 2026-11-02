import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData040
import InducedPentagonsPaper.Generated.PrimitiveRows032

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0480 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41955) = [18, 0, 0, 0, 0, 38, 72, 52, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0480_semantics :
    (Generated.hostChunk040[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[0]).mask = 41955 := by decide +kernel
  have hv : (Generated.hostChunk040[0]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 52, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0480]
  rfl

theorem primitive_values_0481 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41958) = [18, 0, 0, 0, 0, 34, 42, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0481_semantics :
    (Generated.hostChunk040[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[1]).mask = 41958 := by decide +kernel
  have hv : (Generated.hostChunk040[1]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0481]
  rfl

theorem primitive_values_0482 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41959) = [20, 0, 0, 0, 0, 48, 96, 80, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0482_semantics :
    (Generated.hostChunk040[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[2]).mask = 41959 := by decide +kernel
  have hv : (Generated.hostChunk040[2]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 80, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0482]
  rfl

theorem primitive_values_0483 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41964) = [18, 0, 0, 0, 0, 34, 42, 44, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0483_semantics :
    (Generated.hostChunk040[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[3]).mask = 41964 := by decide +kernel
  have hv : (Generated.hostChunk040[3]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 44, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0483]
  rfl

theorem primitive_values_0484 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41965) = [20, 0, 0, 0, 0, 48, 96, 76, 0, 48, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0484_semantics :
    (Generated.hostChunk040[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[4]).mask = 41965 := by decide +kernel
  have hv : (Generated.hostChunk040[4]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 76, 0, 48, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0484]
  rfl

theorem primitive_values_0485 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41966) = [20, 0, 0, 0, 0, 44, 66, 72, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0485_semantics :
    (Generated.hostChunk040[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[5]).mask = 41966 := by decide +kernel
  have hv : (Generated.hostChunk040[5]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 72, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0485]
  rfl

theorem primitive_values_0486 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41967) = [22, 0, 0, 0, 0, 60, 138, 112, 0, 70, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0486_semantics :
    (Generated.hostChunk040[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[6]).mask = 41967 := by decide +kernel
  have hv : (Generated.hostChunk040[6]).primitive.toList = [22, 0, 0, 0, 0, 60, 138, 112, 0, 70, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0486]
  rfl

theorem primitive_values_0487 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41982) = [22, 0, 0, 0, 0, 56, 108, 104, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0487_semantics :
    (Generated.hostChunk040[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[7]).mask = 41982 := by decide +kernel
  have hv : (Generated.hostChunk040[7]).primitive.toList = [22, 0, 0, 0, 0, 56, 108, 104, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0487]
  rfl

theorem primitive_values_0488 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41983) = [24, 0, 0, 0, 0, 74, 204, 152, 0, 108, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0488_semantics :
    (Generated.hostChunk040[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[8]).mask = 41983 := by decide +kernel
  have hv : (Generated.hostChunk040[8]).primitive.toList = [24, 0, 0, 0, 0, 74, 204, 152, 0, 108, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0488]
  rfl

theorem primitive_values_0489 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42047) = [18, 0, 0, 0, 0, 42, 120, 48, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0489_semantics :
    (Generated.hostChunk040[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[9]).mask = 42047 := by decide +kernel
  have hv : (Generated.hostChunk040[9]).primitive.toList = [18, 0, 0, 0, 0, 42, 120, 48, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0489]
  rfl

theorem primitive_values_0490 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42096) = [12, 10, 0, 0, 0, 10, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0490_semantics :
    (Generated.hostChunk040[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[10]).mask = 42096 := by decide +kernel
  have hv : (Generated.hostChunk040[10]).primitive.toList = [12, 10, 0, 0, 0, 10, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0490]
  rfl

theorem primitive_values_0491 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42097) = [14, 0, 0, 0, 0, 18, 12, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0491_semantics :
    (Generated.hostChunk040[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk040[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk040[11]).mask = 42097 := by decide +kernel
  have hv : (Generated.hostChunk040[11]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0491]
  rfl

theorem primitive_chunk_040_semantics :
    ∀ h ∈ Generated.hostChunk040.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk040.toList = [Generated.hostChunk040[0], Generated.hostChunk040[1], Generated.hostChunk040[2], Generated.hostChunk040[3], Generated.hostChunk040[4], Generated.hostChunk040[5], Generated.hostChunk040[6], Generated.hostChunk040[7], Generated.hostChunk040[8], Generated.hostChunk040[9], Generated.hostChunk040[10], Generated.hostChunk040[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0480_semantics
  · exact primitive_host_0481_semantics
  · exact primitive_host_0482_semantics
  · exact primitive_host_0483_semantics
  · exact primitive_host_0484_semantics
  · exact primitive_host_0485_semantics
  · exact primitive_host_0486_semantics
  · exact primitive_host_0487_semantics
  · exact primitive_host_0488_semantics
  · exact primitive_host_0489_semantics
  · exact primitive_host_0490_semantics
  · exact primitive_host_0491_semantics

end InducedPentagons.Paper

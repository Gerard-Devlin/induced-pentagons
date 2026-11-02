import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData050
import InducedPentagonsPaper.Generated.PrimitiveRows042

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0600 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44467) = [20, 0, 0, 0, 0, 42, 60, 64, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0600_semantics :
    (Generated.hostChunk050[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[0]).mask = 44467 := by decide +kernel
  have hv : (Generated.hostChunk050[0]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 64, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0600]
  rfl

theorem primitive_values_0601 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44470) = [20, 0, 0, 0, 0, 42, 60, 66, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0601_semantics :
    (Generated.hostChunk050[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[1]).mask = 44470 := by decide +kernel
  have hv : (Generated.hostChunk050[1]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 66, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0601]
  rfl

theorem primitive_values_0602 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44471) = [22, 0, 0, 0, 0, 56, 114, 102, 0, 52, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0602_semantics :
    (Generated.hostChunk050[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[2]).mask = 44471 := by decide +kernel
  have hv : (Generated.hostChunk050[2]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 102, 0, 52, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0602]
  rfl

theorem primitive_values_0603 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44472) = [18, 10, 6, 0, 6, 30, 24, 44, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0603_semantics :
    (Generated.hostChunk050[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[3]).mask = 44472 := by decide +kernel
  have hv : (Generated.hostChunk050[3]).primitive.toList = [18, 10, 6, 0, 6, 30, 24, 44, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0603]
  rfl

theorem primitive_values_0604 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44473) = [20, 20, 18, 12, 8, 42, 60, 68, 4, 26, 8, 4, 0, 0, 0, 0, 4, 2, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0604_semantics :
    (Generated.hostChunk050[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[4]).mask = 44473 := by decide +kernel
  have hv : (Generated.hostChunk050[4]).primitive.toList = [20, 20, 18, 12, 8, 42, 60, 68, 4, 26, 8, 4, 0, 0, 0, 0, 4, 2, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0604]
  rfl

theorem primitive_values_0605 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44474) = [20, 10, 10, 4, 0, 40, 48, 64, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0605_semantics :
    (Generated.hostChunk050[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[5]).mask = 44474 := by decide +kernel
  have hv : (Generated.hostChunk050[5]).primitive.toList = [20, 10, 10, 4, 0, 40, 48, 64, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0605]
  rfl

theorem primitive_values_0606 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44475) = [22, 0, 0, 0, 0, 54, 102, 98, 0, 38, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0606_semantics :
    (Generated.hostChunk050[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[6]).mask = 44475 := by decide +kernel
  have hv : (Generated.hostChunk050[6]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 98, 0, 38, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0606]
  rfl

theorem primitive_values_0607 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44476) = [20, 0, 0, 0, 0, 42, 60, 74, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0607_semantics :
    (Generated.hostChunk050[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[7]).mask = 44476 := by decide +kernel
  have hv : (Generated.hostChunk050[7]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 74, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0607]
  rfl

theorem primitive_values_0608 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44477) = [22, 0, 0, 0, 0, 56, 114, 106, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0608_semantics :
    (Generated.hostChunk050[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[8]).mask = 44477 := by decide +kernel
  have hv : (Generated.hostChunk050[8]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 106, 0, 58, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0608]
  rfl

theorem primitive_values_0609 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44478) = [22, 0, 0, 0, 0, 54, 102, 100, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0609_semantics :
    (Generated.hostChunk050[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[9]).mask = 44478 := by decide +kernel
  have hv : (Generated.hostChunk050[9]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 100, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0609]
  rfl

theorem primitive_values_0610 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44479) = [24, 0, 0, 0, 0, 70, 180, 142, 0, 90, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0610_semantics :
    (Generated.hostChunk050[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[10]).mask = 44479 := by decide +kernel
  have hv : (Generated.hostChunk050[10]).primitive.toList = [24, 0, 0, 0, 0, 70, 180, 142, 0, 90, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0610]
  rfl

theorem primitive_values_0611 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44526) = [22, 0, 0, 0, 0, 56, 102, 114, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0611_semantics :
    (Generated.hostChunk050[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk050[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk050[11]).mask = 44526 := by decide +kernel
  have hv : (Generated.hostChunk050[11]).primitive.toList = [22, 0, 0, 0, 0, 56, 102, 114, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0611]
  rfl

theorem primitive_chunk_050_semantics :
    ∀ h ∈ Generated.hostChunk050.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk050.toList = [Generated.hostChunk050[0], Generated.hostChunk050[1], Generated.hostChunk050[2], Generated.hostChunk050[3], Generated.hostChunk050[4], Generated.hostChunk050[5], Generated.hostChunk050[6], Generated.hostChunk050[7], Generated.hostChunk050[8], Generated.hostChunk050[9], Generated.hostChunk050[10], Generated.hostChunk050[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0600_semantics
  · exact primitive_host_0601_semantics
  · exact primitive_host_0602_semantics
  · exact primitive_host_0603_semantics
  · exact primitive_host_0604_semantics
  · exact primitive_host_0605_semantics
  · exact primitive_host_0606_semantics
  · exact primitive_host_0607_semantics
  · exact primitive_host_0608_semantics
  · exact primitive_host_0609_semantics
  · exact primitive_host_0610_semantics
  · exact primitive_host_0611_semantics

end InducedPentagons.Paper

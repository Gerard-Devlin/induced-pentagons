import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData041
import InducedPentagonsPaper.Generated.PrimitiveRows033

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0492 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42099) = [16, 0, 0, 0, 0, 28, 36, 34, 0, 20, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0492_semantics :
    (Generated.hostChunk041[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[0]).mask = 42099 := by decide +kernel
  have hv : (Generated.hostChunk041[0]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 34, 0, 20, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0492]
  rfl

theorem primitive_values_0493 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42100) = [14, 10, 2, 0, 2, 16, 6, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0493_semantics :
    (Generated.hostChunk041[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[1]).mask = 42100 := by decide +kernel
  have hv : (Generated.hostChunk041[1]).primitive.toList = [14, 10, 2, 0, 2, 16, 6, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0493]
  rfl

theorem primitive_values_0494 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42101) = [16, 0, 0, 0, 0, 26, 30, 34, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0494_semantics :
    (Generated.hostChunk041[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[2]).mask = 42101 := by decide +kernel
  have hv : (Generated.hostChunk041[2]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 34, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0494]
  rfl

theorem primitive_values_0495 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42103) = [18, 0, 0, 0, 0, 38, 72, 54, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0495_semantics :
    (Generated.hostChunk041[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[3]).mask = 42103 := by decide +kernel
  have hv : (Generated.hostChunk041[3]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 54, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0495]
  rfl

theorem primitive_values_0496 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42108) = [16, 10, 4, 4, 4, 24, 24, 26, 4, 4, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0496_semantics :
    (Generated.hostChunk041[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[4]).mask = 42108 := by decide +kernel
  have hv : (Generated.hostChunk041[4]).primitive.toList = [16, 10, 4, 4, 4, 24, 24, 26, 4, 4, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0496]
  rfl

theorem primitive_values_0497 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42109) = [18, 0, 0, 0, 0, 36, 66, 48, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0497_semantics :
    (Generated.hostChunk041[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[5]).mask = 42109 := by decide +kernel
  have hv : (Generated.hostChunk041[5]).primitive.toList = [18, 0, 0, 0, 0, 36, 66, 48, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0497]
  rfl

theorem primitive_values_0498 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42111) = [20, 0, 0, 0, 0, 50, 132, 74, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0498_semantics :
    (Generated.hostChunk041[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[6]).mask = 42111 := by decide +kernel
  have hv : (Generated.hostChunk041[6]).primitive.toList = [20, 0, 0, 0, 0, 50, 132, 74, 0, 40, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0498]
  rfl

theorem primitive_values_0499 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42218) = [16, 20, 10, 0, 4, 24, 18, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0499_semantics :
    (Generated.hostChunk041[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[7]).mask = 42218 := by decide +kernel
  have hv : (Generated.hostChunk041[7]).primitive.toList = [16, 20, 10, 0, 4, 24, 18, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0499]
  rfl

theorem primitive_values_0500 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42219) = [18, 0, 0, 0, 0, 36, 54, 56, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0500_semantics :
    (Generated.hostChunk041[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[8]).mask = 42219 := by decide +kernel
  have hv : (Generated.hostChunk041[8]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 56, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0500]
  rfl

theorem primitive_values_0501 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42220) = [16, 0, 0, 0, 0, 24, 18, 30, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0501_semantics :
    (Generated.hostChunk041[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[9]).mask = 42220 := by decide +kernel
  have hv : (Generated.hostChunk041[9]).primitive.toList = [16, 0, 0, 0, 0, 24, 18, 30, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0501]
  rfl

theorem primitive_values_0502 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42221) = [18, 0, 0, 0, 0, 36, 54, 52, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0502_semantics :
    (Generated.hostChunk041[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[10]).mask = 42221 := by decide +kernel
  have hv : (Generated.hostChunk041[10]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 52, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0502]
  rfl

theorem primitive_values_0503 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42222) = [18, 0, 0, 0, 0, 34, 42, 54, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0503_semantics :
    (Generated.hostChunk041[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk041[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk041[11]).mask = 42222 := by decide +kernel
  have hv : (Generated.hostChunk041[11]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 54, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0503]
  rfl

theorem primitive_chunk_041_semantics :
    ∀ h ∈ Generated.hostChunk041.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk041.toList = [Generated.hostChunk041[0], Generated.hostChunk041[1], Generated.hostChunk041[2], Generated.hostChunk041[3], Generated.hostChunk041[4], Generated.hostChunk041[5], Generated.hostChunk041[6], Generated.hostChunk041[7], Generated.hostChunk041[8], Generated.hostChunk041[9], Generated.hostChunk041[10], Generated.hostChunk041[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0492_semantics
  · exact primitive_host_0493_semantics
  · exact primitive_host_0494_semantics
  · exact primitive_host_0495_semantics
  · exact primitive_host_0496_semantics
  · exact primitive_host_0497_semantics
  · exact primitive_host_0498_semantics
  · exact primitive_host_0499_semantics
  · exact primitive_host_0500_semantics
  · exact primitive_host_0501_semantics
  · exact primitive_host_0502_semantics
  · exact primitive_host_0503_semantics

end InducedPentagons.Paper

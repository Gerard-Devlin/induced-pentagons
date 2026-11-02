import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData010
import InducedPentagonsPaper.Generated.PrimitiveRows002

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0120 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2551) = [18, 0, 0, 0, 0, 44, 96, 64, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0120_semantics :
    (Generated.hostChunk010[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[0]).mask = 2551 := by decide +kernel
  have hv : (Generated.hostChunk010[0]).primitive.toList = [18, 0, 0, 0, 0, 44, 96, 64, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0120]
  rfl

theorem primitive_values_0121 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2552) = [14, 0, 0, 0, 0, 18, 12, 12, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0121_semantics :
    (Generated.hostChunk010[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[1]).mask = 2552 := by decide +kernel
  have hv : (Generated.hostChunk010[1]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 12, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0121]
  rfl

theorem primitive_values_0122 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2553) = [16, 0, 0, 0, 0, 30, 48, 32, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0122_semantics :
    (Generated.hostChunk010[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[2]).mask = 2553 := by decide +kernel
  have hv : (Generated.hostChunk010[2]).primitive.toList = [16, 0, 0, 0, 0, 30, 48, 32, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0122]
  rfl

theorem primitive_values_0123 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2554) = [16, 0, 0, 0, 0, 28, 36, 32, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0123_semantics :
    (Generated.hostChunk010[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[3]).mask = 2554 := by decide +kernel
  have hv : (Generated.hostChunk010[3]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 32, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0123]
  rfl

theorem primitive_values_0124 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2555) = [18, 0, 0, 0, 0, 42, 90, 58, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0124_semantics :
    (Generated.hostChunk010[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[4]).mask = 2555 := by decide +kernel
  have hv : (Generated.hostChunk010[4]).primitive.toList = [18, 0, 0, 0, 0, 42, 90, 58, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0124]
  rfl

theorem primitive_values_0125 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2558) = [18, 0, 0, 0, 0, 40, 78, 56, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0125_semantics :
    (Generated.hostChunk010[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[5]).mask = 2558 := by decide +kernel
  have hv : (Generated.hostChunk010[5]).primitive.toList = [18, 0, 0, 0, 0, 40, 78, 56, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0125]
  rfl

theorem primitive_values_0126 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2559) = [20, 0, 0, 0, 0, 56, 156, 88, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0126_semantics :
    (Generated.hostChunk010[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[6]).mask = 2559 := by decide +kernel
  have hv : (Generated.hostChunk010[6]).primitive.toList = [20, 0, 0, 0, 0, 56, 156, 88, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0126]
  rfl

theorem primitive_values_0127 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2840) = [10, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0127_semantics :
    (Generated.hostChunk010[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[7]).mask = 2840 := by decide +kernel
  have hv : (Generated.hostChunk010[7]).primitive.toList = [10, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0127]
  rfl

theorem primitive_values_0128 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2841) = [12, 0, 0, 0, 0, 16, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0128_semantics :
    (Generated.hostChunk010[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[8]).mask = 2841 := by decide +kernel
  have hv : (Generated.hostChunk010[8]).primitive.toList = [12, 0, 0, 0, 0, 16, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0128]
  rfl

theorem primitive_values_0129 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2842) = [12, 0, 0, 0, 0, 14, 6, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0129_semantics :
    (Generated.hostChunk010[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[9]).mask = 2842 := by decide +kernel
  have hv : (Generated.hostChunk010[9]).primitive.toList = [12, 0, 0, 0, 0, 14, 6, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0129]
  rfl

theorem primitive_values_0130 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2843) = [14, 0, 0, 0, 0, 24, 30, 26, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0130_semantics :
    (Generated.hostChunk010[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[10]).mask = 2843 := by decide +kernel
  have hv : (Generated.hostChunk010[10]).primitive.toList = [14, 0, 0, 0, 0, 24, 30, 26, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0130]
  rfl

theorem primitive_values_0131 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2846) = [14, 0, 0, 0, 0, 22, 24, 24, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0131_semantics :
    (Generated.hostChunk010[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk010[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk010[11]).mask = 2846 := by decide +kernel
  have hv : (Generated.hostChunk010[11]).primitive.toList = [14, 0, 0, 0, 0, 22, 24, 24, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0131]
  rfl

theorem primitive_chunk_010_semantics :
    ∀ h ∈ Generated.hostChunk010.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk010.toList = [Generated.hostChunk010[0], Generated.hostChunk010[1], Generated.hostChunk010[2], Generated.hostChunk010[3], Generated.hostChunk010[4], Generated.hostChunk010[5], Generated.hostChunk010[6], Generated.hostChunk010[7], Generated.hostChunk010[8], Generated.hostChunk010[9], Generated.hostChunk010[10], Generated.hostChunk010[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0120_semantics
  · exact primitive_host_0121_semantics
  · exact primitive_host_0122_semantics
  · exact primitive_host_0123_semantics
  · exact primitive_host_0124_semantics
  · exact primitive_host_0125_semantics
  · exact primitive_host_0126_semantics
  · exact primitive_host_0127_semantics
  · exact primitive_host_0128_semantics
  · exact primitive_host_0129_semantics
  · exact primitive_host_0130_semantics
  · exact primitive_host_0131_semantics

end InducedPentagons.Paper

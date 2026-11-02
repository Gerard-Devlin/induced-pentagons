import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData026
import InducedPentagonsPaper.Generated.PrimitiveRows018

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0312 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7931) = [22, 0, 0, 0, 0, 60, 144, 110, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0312_semantics :
    (Generated.hostChunk026[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[0]).mask = 7931 := by decide +kernel
  have hv : (Generated.hostChunk026[0]).primitive.toList = [22, 0, 0, 0, 0, 60, 144, 110, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0312]
  rfl

theorem primitive_values_0313 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7932) = [20, 20, 20, 16, 0, 42, 60, 72, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0313_semantics :
    (Generated.hostChunk026[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[1]).mask = 7932 := by decide +kernel
  have hv : (Generated.hostChunk026[1]).primitive.toList = [20, 20, 20, 16, 0, 42, 60, 72, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0313]
  rfl

theorem primitive_values_0314 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7933) = [22, 0, 0, 0, 0, 58, 132, 108, 0, 48, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0314_semantics :
    (Generated.hostChunk026[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[2]).mask = 7933 := by decide +kernel
  have hv : (Generated.hostChunk026[2]).primitive.toList = [22, 0, 0, 0, 0, 58, 132, 108, 0, 48, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0314]
  rfl

theorem primitive_values_0315 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7934) = [22, 0, 0, 0, 0, 56, 114, 106, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0315_semantics :
    (Generated.hostChunk026[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[3]).mask = 7934 := by decide +kernel
  have hv : (Generated.hostChunk026[3]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 106, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0315]
  rfl

theorem primitive_values_0316 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7935) = [24, 0, 0, 0, 0, 74, 210, 152, 0, 100, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0316_semantics :
    (Generated.hostChunk026[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[4]).mask = 7935 := by decide +kernel
  have hv : (Generated.hostChunk026[4]).primitive.toList = [24, 0, 0, 0, 0, 74, 210, 152, 0, 100, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0316]
  rfl

theorem primitive_values_0317 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 8124) = [20, 0, 0, 0, 0, 42, 60, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0317_semantics :
    (Generated.hostChunk026[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[5]).mask = 8124 := by decide +kernel
  have hv : (Generated.hostChunk026[5]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0317]
  rfl

theorem primitive_values_0318 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 8125) = [22, 0, 0, 0, 0, 58, 132, 112, 0, 52, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0318_semantics :
    (Generated.hostChunk026[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[6]).mask = 8125 := by decide +kernel
  have hv : (Generated.hostChunk026[6]).primitive.toList = [22, 0, 0, 0, 0, 58, 132, 112, 0, 52, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0318]
  rfl

theorem primitive_values_0319 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 8126) = [22, 0, 0, 0, 0, 54, 102, 104, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0319_semantics :
    (Generated.hostChunk026[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[7]).mask = 8126 := by decide +kernel
  have hv : (Generated.hostChunk026[7]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 104, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0319]
  rfl

theorem primitive_values_0320 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 8127) = [24, 0, 0, 0, 0, 72, 198, 148, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0320_semantics :
    (Generated.hostChunk026[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[8]).mask = 8127 := by decide +kernel
  have hv : (Generated.hostChunk026[8]).primitive.toList = [24, 0, 0, 0, 0, 72, 198, 148, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0320]
  rfl

theorem primitive_values_0321 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 8190) = [24, 0, 0, 0, 0, 68, 156, 144, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0321_semantics :
    (Generated.hostChunk026[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[9]).mask = 8190 := by decide +kernel
  have hv : (Generated.hostChunk026[9]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 144, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0321]
  rfl

theorem primitive_values_0322 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 8191) = [26, 0, 0, 0, 0, 88, 276, 200, 0, 144, 40, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 88] := by
  decide +kernel

theorem primitive_host_0322_semantics :
    (Generated.hostChunk026[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[10]).mask = 8191 := by decide +kernel
  have hv : (Generated.hostChunk026[10]).primitive.toList = [26, 0, 0, 0, 0, 88, 276, 200, 0, 144, 40, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 88] := by decide +kernel
  rw [hm, hv, primitive_values_0322]
  rfl

theorem primitive_values_0323 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15260) = [18, 0, 0, 0, 0, 36, 36, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0323_semantics :
    (Generated.hostChunk026[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk026[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk026[11]).mask = 15260 := by decide +kernel
  have hv : (Generated.hostChunk026[11]).primitive.toList = [18, 0, 0, 0, 0, 36, 36, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0323]
  rfl

theorem primitive_chunk_026_semantics :
    ∀ h ∈ Generated.hostChunk026.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk026.toList = [Generated.hostChunk026[0], Generated.hostChunk026[1], Generated.hostChunk026[2], Generated.hostChunk026[3], Generated.hostChunk026[4], Generated.hostChunk026[5], Generated.hostChunk026[6], Generated.hostChunk026[7], Generated.hostChunk026[8], Generated.hostChunk026[9], Generated.hostChunk026[10], Generated.hostChunk026[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0312_semantics
  · exact primitive_host_0313_semantics
  · exact primitive_host_0314_semantics
  · exact primitive_host_0315_semantics
  · exact primitive_host_0316_semantics
  · exact primitive_host_0317_semantics
  · exact primitive_host_0318_semantics
  · exact primitive_host_0319_semantics
  · exact primitive_host_0320_semantics
  · exact primitive_host_0321_semantics
  · exact primitive_host_0322_semantics
  · exact primitive_host_0323_semantics

end InducedPentagons.Paper

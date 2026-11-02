import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData062
import InducedPentagonsPaper.Generated.PrimitiveRows054

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0744 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59071) = [24, 0, 0, 0, 0, 68, 168, 140, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0744_semantics :
    (Generated.hostChunk062[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[0]).mask = 59071 := by decide +kernel
  have hv : (Generated.hostChunk062[0]).primitive.toList = [24, 0, 0, 0, 0, 68, 168, 140, 0, 76, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0744]
  rfl

theorem primitive_values_0745 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59126) = [22, 0, 0, 0, 0, 54, 90, 108, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0745_semantics :
    (Generated.hostChunk062[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[1]).mask = 59126 := by decide +kernel
  have hv : (Generated.hostChunk062[1]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 108, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0745]
  rfl

theorem primitive_values_0746 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59127) = [24, 0, 0, 0, 0, 70, 162, 152, 0, 106, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0746_semantics :
    (Generated.hostChunk062[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[2]).mask = 59127 := by decide +kernel
  have hv : (Generated.hostChunk062[2]).primitive.toList = [24, 0, 0, 0, 0, 70, 162, 152, 0, 106, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0746]
  rfl

theorem primitive_values_0747 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59130) = [22, 30, 32, 28, 20, 52, 84, 98, 16, 40, 16, 8, 0, 0, 0, 0, 16, 8, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0747_semantics :
    (Generated.hostChunk062[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[3]).mask = 59130 := by decide +kernel
  have hv : (Generated.hostChunk062[3]).primitive.toList = [22, 30, 32, 28, 20, 52, 84, 98, 16, 40, 16, 8, 0, 0, 0, 0, 16, 8, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0747]
  rfl

theorem primitive_values_0748 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59131) = [24, 0, 0, 0, 0, 68, 156, 144, 0, 92, 12, 0, 4, 48, 0, 8, 0, 0, 4, 4, 0, 60] := by
  decide +kernel

theorem primitive_host_0748_semantics :
    (Generated.hostChunk062[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[4]).mask = 59131 := by decide +kernel
  have hv : (Generated.hostChunk062[4]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 144, 0, 92, 12, 0, 4, 48, 0, 8, 0, 0, 4, 4, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0748]
  rfl

theorem primitive_values_0749 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59132) = [22, 0, 0, 0, 0, 50, 72, 92, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0749_semantics :
    (Generated.hostChunk062[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[5]).mask = 59132 := by decide +kernel
  have hv : (Generated.hostChunk062[5]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 92, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0749]
  rfl

theorem primitive_values_0750 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59133) = [24, 0, 0, 0, 0, 66, 144, 136, 0, 70, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0750_semantics :
    (Generated.hostChunk062[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[6]).mask = 59133 := by decide +kernel
  have hv : (Generated.hostChunk062[6]).primitive.toList = [24, 0, 0, 0, 0, 66, 144, 136, 0, 70, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0750]
  rfl

theorem primitive_values_0751 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59134) = [24, 0, 0, 0, 0, 64, 126, 132, 0, 52, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0751_semantics :
    (Generated.hostChunk062[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[7]).mask = 59134 := by decide +kernel
  have hv : (Generated.hostChunk062[7]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 132, 0, 52, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0751]
  rfl

theorem primitive_values_0752 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59135) = [26, 0, 0, 0, 0, 82, 222, 186, 0, 128, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by
  decide +kernel

theorem primitive_host_0752_semantics :
    (Generated.hostChunk062[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[8]).mask = 59135 := by decide +kernel
  have hv : (Generated.hostChunk062[8]).primitive.toList = [26, 0, 0, 0, 0, 82, 222, 186, 0, 128, 28, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 76] := by decide +kernel
  rw [hm, hv, primitive_values_0752]
  rfl

theorem primitive_values_0753 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59324) = [22, 0, 0, 0, 0, 50, 72, 100, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0753_semantics :
    (Generated.hostChunk062[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[9]).mask = 59324 := by decide +kernel
  have hv : (Generated.hostChunk062[9]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 100, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0753]
  rfl

theorem primitive_values_0754 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59325) = [24, 0, 0, 0, 0, 66, 144, 140, 0, 76, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0754_semantics :
    (Generated.hostChunk062[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[10]).mask = 59325 := by decide +kernel
  have hv : (Generated.hostChunk062[10]).primitive.toList = [24, 0, 0, 0, 0, 66, 144, 140, 0, 76, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0754]
  rfl

theorem primitive_values_0755 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 59326) = [24, 0, 0, 0, 0, 62, 114, 128, 0, 38, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0755_semantics :
    (Generated.hostChunk062[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk062[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk062[11]).mask = 59326 := by decide +kernel
  have hv : (Generated.hostChunk062[11]).primitive.toList = [24, 0, 0, 0, 0, 62, 114, 128, 0, 38, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0755]
  rfl

theorem primitive_chunk_062_semantics :
    ∀ h ∈ Generated.hostChunk062.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk062.toList = [Generated.hostChunk062[0], Generated.hostChunk062[1], Generated.hostChunk062[2], Generated.hostChunk062[3], Generated.hostChunk062[4], Generated.hostChunk062[5], Generated.hostChunk062[6], Generated.hostChunk062[7], Generated.hostChunk062[8], Generated.hostChunk062[9], Generated.hostChunk062[10], Generated.hostChunk062[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0744_semantics
  · exact primitive_host_0745_semantics
  · exact primitive_host_0746_semantics
  · exact primitive_host_0747_semantics
  · exact primitive_host_0748_semantics
  · exact primitive_host_0749_semantics
  · exact primitive_host_0750_semantics
  · exact primitive_host_0751_semantics
  · exact primitive_host_0752_semantics
  · exact primitive_host_0753_semantics
  · exact primitive_host_0754_semantics
  · exact primitive_host_0755_semantics

end InducedPentagons.Paper

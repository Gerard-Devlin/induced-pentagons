import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData055
import InducedPentagonsPaper.Generated.PrimitiveRows047

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0660 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48119) = [26, 0, 0, 0, 0, 84, 216, 200, 0, 146, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0660_semantics :
    (Generated.hostChunk055[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[0]).mask = 48119 := by decide +kernel
  have hv : (Generated.hostChunk055[0]).primitive.toList = [26, 0, 0, 0, 0, 84, 216, 200, 0, 146, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0660]
  rfl

theorem primitive_values_0661 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48124) = [24, 0, 0, 0, 0, 66, 126, 144, 0, 70, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0661_semantics :
    (Generated.hostChunk055[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[1]).mask = 48124 := by decide +kernel
  have hv : (Generated.hostChunk055[1]).primitive.toList = [24, 0, 0, 0, 0, 66, 126, 144, 0, 70, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0661]
  rfl

theorem primitive_values_0662 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48125) = [26, 0, 0, 0, 0, 82, 198, 196, 0, 126, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0662_semantics :
    (Generated.hostChunk055[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[2]).mask = 48125 := by decide +kernel
  have hv : (Generated.hostChunk055[2]).primitive.toList = [26, 0, 0, 0, 0, 82, 198, 196, 0, 126, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0662]
  rfl

theorem primitive_values_0663 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48127) = [28, 0, 0, 0, 0, 100, 294, 260, 0, 214, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0663_semantics :
    (Generated.hostChunk055[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[3]).mask = 48127 := by decide +kernel
  have hv : (Generated.hostChunk055[3]).primitive.toList = [28, 0, 0, 0, 0, 100, 294, 260, 0, 214, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0663]
  rfl

theorem primitive_values_0664 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48560) = [18, 0, 0, 0, 0, 30, 24, 40, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0664_semantics :
    (Generated.hostChunk055[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[4]).mask = 48560 := by decide +kernel
  have hv : (Generated.hostChunk055[4]).primitive.toList = [18, 0, 0, 0, 0, 30, 24, 40, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0664]
  rfl

theorem primitive_values_0665 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48561) = [20, 20, 20, 8, 0, 40, 48, 60, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0665_semantics :
    (Generated.hostChunk055[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[5]).mask = 48561 := by decide +kernel
  have hv : (Generated.hostChunk055[5]).primitive.toList = [20, 20, 20, 8, 0, 40, 48, 60, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0665]
  rfl

theorem primitive_values_0666 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48563) = [22, 0, 0, 0, 0, 52, 84, 92, 0, 32, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0666_semantics :
    (Generated.hostChunk055[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[6]).mask = 48563 := by decide +kernel
  have hv : (Generated.hostChunk055[6]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 92, 0, 32, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0666]
  rfl

theorem primitive_values_0667 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48564) = [20, 0, 0, 0, 0, 40, 48, 68, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0667_semantics :
    (Generated.hostChunk055[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[7]).mask = 48564 := by decide +kernel
  have hv : (Generated.hostChunk055[7]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 68, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0667]
  rfl

theorem primitive_values_0668 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48565) = [22, 10, 12, 8, 0, 52, 84, 96, 0, 38, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0668_semantics :
    (Generated.hostChunk055[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[8]).mask = 48565 := by decide +kernel
  have hv : (Generated.hostChunk055[8]).primitive.toList = [22, 10, 12, 8, 0, 52, 84, 96, 0, 38, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0668]
  rfl

theorem primitive_values_0669 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48567) = [24, 0, 0, 0, 0, 66, 138, 136, 0, 68, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0669_semantics :
    (Generated.hostChunk055[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[9]).mask = 48567 := by decide +kernel
  have hv : (Generated.hostChunk055[9]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 136, 0, 68, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0669]
  rfl

theorem primitive_values_0670 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48572) = [22, 0, 0, 0, 0, 52, 84, 104, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0670_semantics :
    (Generated.hostChunk055[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[10]).mask = 48572 := by decide +kernel
  have hv : (Generated.hostChunk055[10]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 104, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0670]
  rfl

theorem primitive_values_0671 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48573) = [24, 0, 0, 0, 0, 66, 138, 140, 0, 74, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0671_semantics :
    (Generated.hostChunk055[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk055[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk055[11]).mask = 48573 := by decide +kernel
  have hv : (Generated.hostChunk055[11]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 140, 0, 74, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0671]
  rfl

theorem primitive_chunk_055_semantics :
    ∀ h ∈ Generated.hostChunk055.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk055.toList = [Generated.hostChunk055[0], Generated.hostChunk055[1], Generated.hostChunk055[2], Generated.hostChunk055[3], Generated.hostChunk055[4], Generated.hostChunk055[5], Generated.hostChunk055[6], Generated.hostChunk055[7], Generated.hostChunk055[8], Generated.hostChunk055[9], Generated.hostChunk055[10], Generated.hostChunk055[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0660_semantics
  · exact primitive_host_0661_semantics
  · exact primitive_host_0662_semantics
  · exact primitive_host_0663_semantics
  · exact primitive_host_0664_semantics
  · exact primitive_host_0665_semantics
  · exact primitive_host_0666_semantics
  · exact primitive_host_0667_semantics
  · exact primitive_host_0668_semantics
  · exact primitive_host_0669_semantics
  · exact primitive_host_0670_semantics
  · exact primitive_host_0671_semantics

end InducedPentagons.Paper

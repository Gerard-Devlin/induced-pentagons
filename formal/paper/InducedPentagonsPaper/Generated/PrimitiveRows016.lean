import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData016
import InducedPentagonsPaper.Generated.PrimitiveRows008

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0192 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6559) = [18, 0, 0, 0, 0, 44, 84, 72, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0192_semantics :
    (Generated.hostChunk016[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[0]).mask = 6559 := by decide +kernel
  have hv : (Generated.hostChunk016[0]).primitive.toList = [18, 0, 0, 0, 0, 44, 84, 72, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0192]
  rfl

theorem primitive_values_0193 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6576) = [12, 0, 0, 0, 0, 10, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0193_semantics :
    (Generated.hostChunk016[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[1]).mask = 6576 := by decide +kernel
  have hv : (Generated.hostChunk016[1]).primitive.toList = [12, 0, 0, 0, 0, 10, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0193]
  rfl

theorem primitive_values_0194 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6577) = [14, 0, 0, 0, 0, 18, 12, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0194_semantics :
    (Generated.hostChunk016[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[2]).mask = 6577 := by decide +kernel
  have hv : (Generated.hostChunk016[2]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0194]
  rfl

theorem primitive_values_0195 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6579) = [16, 0, 0, 0, 0, 28, 36, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0195_semantics :
    (Generated.hostChunk016[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[3]).mask = 6579 := by decide +kernel
  have hv : (Generated.hostChunk016[3]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0195]
  rfl

theorem primitive_values_0196 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6581) = [16, 0, 0, 0, 0, 28, 36, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0196_semantics :
    (Generated.hostChunk016[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[4]).mask = 6581 := by decide +kernel
  have hv : (Generated.hostChunk016[4]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0196]
  rfl

theorem primitive_values_0197 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6583) = [18, 0, 0, 0, 0, 40, 78, 60, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0197_semantics :
    (Generated.hostChunk016[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[5]).mask = 6583 := by decide +kernel
  have hv : (Generated.hostChunk016[5]).primitive.toList = [18, 0, 0, 0, 0, 40, 78, 60, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0197]
  rfl

theorem primitive_values_0198 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6591) = [20, 0, 0, 0, 0, 54, 144, 88, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0198_semantics :
    (Generated.hostChunk016[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[6]).mask = 6591 := by decide +kernel
  have hv : (Generated.hostChunk016[6]).primitive.toList = [20, 0, 0, 0, 0, 54, 144, 88, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0198]
  rfl

theorem primitive_values_0199 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6607) = [18, 0, 0, 0, 0, 48, 84, 84, 0, 72, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0199_semantics :
    (Generated.hostChunk016[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[7]).mask = 6607 := by decide +kernel
  have hv : (Generated.hostChunk016[7]).primitive.toList = [18, 0, 0, 0, 0, 48, 84, 84, 0, 72, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0199]
  rfl

theorem primitive_values_0200 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6612) = [14, 0, 0, 0, 0, 22, 18, 24, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0200_semantics :
    (Generated.hostChunk016[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[8]).mask = 6612 := by decide +kernel
  have hv : (Generated.hostChunk016[8]).primitive.toList = [14, 0, 0, 0, 0, 22, 18, 24, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0200]
  rfl

theorem primitive_values_0201 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6613) = [16, 0, 0, 0, 0, 32, 42, 44, 0, 22, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0201_semantics :
    (Generated.hostChunk016[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[9]).mask = 6613 := by decide +kernel
  have hv : (Generated.hostChunk016[9]).primitive.toList = [16, 0, 0, 0, 0, 32, 42, 44, 0, 22, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0201]
  rfl

theorem primitive_values_0202 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6615) = [18, 0, 0, 0, 0, 44, 78, 72, 0, 50, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0202_semantics :
    (Generated.hostChunk016[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[10]).mask = 6615 := by decide +kernel
  have hv : (Generated.hostChunk016[10]).primitive.toList = [18, 0, 0, 0, 0, 44, 78, 72, 0, 50, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0202]
  rfl

theorem primitive_values_0203 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6620) = [16, 0, 0, 0, 0, 30, 30, 44, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0203_semantics :
    (Generated.hostChunk016[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk016[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk016[11]).mask = 6620 := by decide +kernel
  have hv : (Generated.hostChunk016[11]).primitive.toList = [16, 0, 0, 0, 0, 30, 30, 44, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0203]
  rfl

theorem primitive_chunk_016_semantics :
    ∀ h ∈ Generated.hostChunk016.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk016.toList = [Generated.hostChunk016[0], Generated.hostChunk016[1], Generated.hostChunk016[2], Generated.hostChunk016[3], Generated.hostChunk016[4], Generated.hostChunk016[5], Generated.hostChunk016[6], Generated.hostChunk016[7], Generated.hostChunk016[8], Generated.hostChunk016[9], Generated.hostChunk016[10], Generated.hostChunk016[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0192_semantics
  · exact primitive_host_0193_semantics
  · exact primitive_host_0194_semantics
  · exact primitive_host_0195_semantics
  · exact primitive_host_0196_semantics
  · exact primitive_host_0197_semantics
  · exact primitive_host_0198_semantics
  · exact primitive_host_0199_semantics
  · exact primitive_host_0200_semantics
  · exact primitive_host_0201_semantics
  · exact primitive_host_0202_semantics
  · exact primitive_host_0203_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData039
import InducedPentagonsPaper.Generated.PrimitiveRows031

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0468 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40695) = [24, 0, 0, 0, 0, 70, 168, 148, 0, 92, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0468_semantics :
    (Generated.hostChunk039[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[0]).mask = 40695 := by decide +kernel
  have hv : (Generated.hostChunk039[0]).primitive.toList = [24, 0, 0, 0, 0, 70, 168, 148, 0, 92, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0468]
  rfl

theorem primitive_values_0469 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40698) = [22, 20, 24, 16, 0, 52, 84, 98, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0469_semantics :
    (Generated.hostChunk039[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[1]).mask = 40698 := by decide +kernel
  have hv : (Generated.hostChunk039[1]).primitive.toList = [22, 20, 24, 16, 0, 52, 84, 98, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0469]
  rfl

theorem primitive_values_0470 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40699) = [24, 0, 0, 0, 0, 68, 156, 140, 0, 72, 28, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0470_semantics :
    (Generated.hostChunk039[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[2]).mask = 40699 := by decide +kernel
  have hv : (Generated.hostChunk039[2]).primitive.toList = [24, 0, 0, 0, 0, 68, 156, 140, 0, 72, 28, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0470]
  rfl

theorem primitive_values_0471 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40702) = [24, 0, 0, 0, 0, 66, 138, 140, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0471_semantics :
    (Generated.hostChunk039[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[3]).mask = 40702 := by decide +kernel
  have hv : (Generated.hostChunk039[3]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 140, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0471]
  rfl

theorem primitive_values_0472 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40703) = [26, 0, 0, 0, 0, 84, 234, 192, 0, 132, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0472_semantics :
    (Generated.hostChunk039[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[4]).mask = 40703 := by decide +kernel
  have hv : (Generated.hostChunk039[4]).primitive.toList = [26, 0, 0, 0, 0, 84, 234, 192, 0, 132, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0472]
  rfl

theorem primitive_values_0473 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40958) = [26, 0, 0, 0, 0, 80, 192, 188, 0, 96, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0473_semantics :
    (Generated.hostChunk039[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[5]).mask = 40958 := by decide +kernel
  have hv : (Generated.hostChunk039[5]).primitive.toList = [26, 0, 0, 0, 0, 80, 192, 188, 0, 96, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0473]
  rfl

theorem primitive_values_0474 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 40959) = [28, 0, 0, 0, 0, 100, 312, 252, 0, 200, 28, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 148] := by
  decide +kernel

theorem primitive_host_0474_semantics :
    (Generated.hostChunk039[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[6]).mask = 40959 := by decide +kernel
  have hv : (Generated.hostChunk039[6]).primitive.toList = [28, 0, 0, 0, 0, 100, 312, 252, 0, 200, 28, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 148] := by decide +kernel
  rw [hm, hv, primitive_values_0474]
  rfl

theorem primitive_values_0475 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41950) = [20, 0, 0, 0, 0, 48, 72, 88, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0475_semantics :
    (Generated.hostChunk039[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[7]).mask = 41950 := by decide +kernel
  have hv : (Generated.hostChunk039[7]).primitive.toList = [20, 0, 0, 0, 0, 48, 72, 88, 0, 32, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0475]
  rfl

theorem primitive_values_0476 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41951) = [22, 0, 0, 0, 0, 64, 144, 128, 0, 96, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0476_semantics :
    (Generated.hostChunk039[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[8]).mask = 41951 := by decide +kernel
  have hv : (Generated.hostChunk039[8]).primitive.toList = [22, 0, 0, 0, 0, 64, 144, 128, 0, 96, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0476]
  rfl

theorem primitive_values_0477 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41952) = [14, 0, 0, 0, 0, 20, 24, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0477_semantics :
    (Generated.hostChunk039[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[9]).mask = 41952 := by decide +kernel
  have hv : (Generated.hostChunk039[9]).primitive.toList = [14, 0, 0, 0, 0, 20, 24, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0477]
  rfl

theorem primitive_values_0478 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41953) = [16, 0, 0, 0, 0, 30, 60, 32, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0478_semantics :
    (Generated.hostChunk039[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[10]).mask = 41953 := by decide +kernel
  have hv : (Generated.hostChunk039[10]).primitive.toList = [16, 0, 0, 0, 0, 30, 60, 32, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0478]
  rfl

theorem primitive_values_0479 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 41954) = [16, 0, 0, 0, 0, 26, 30, 28, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0479_semantics :
    (Generated.hostChunk039[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk039[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk039[11]).mask = 41954 := by decide +kernel
  have hv : (Generated.hostChunk039[11]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 28, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0479]
  rfl

theorem primitive_chunk_039_semantics :
    ∀ h ∈ Generated.hostChunk039.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk039.toList = [Generated.hostChunk039[0], Generated.hostChunk039[1], Generated.hostChunk039[2], Generated.hostChunk039[3], Generated.hostChunk039[4], Generated.hostChunk039[5], Generated.hostChunk039[6], Generated.hostChunk039[7], Generated.hostChunk039[8], Generated.hostChunk039[9], Generated.hostChunk039[10], Generated.hostChunk039[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0468_semantics
  · exact primitive_host_0469_semantics
  · exact primitive_host_0470_semantics
  · exact primitive_host_0471_semantics
  · exact primitive_host_0472_semantics
  · exact primitive_host_0473_semantics
  · exact primitive_host_0474_semantics
  · exact primitive_host_0475_semantics
  · exact primitive_host_0476_semantics
  · exact primitive_host_0477_semantics
  · exact primitive_host_0478_semantics
  · exact primitive_host_0479_semantics

end InducedPentagons.Paper

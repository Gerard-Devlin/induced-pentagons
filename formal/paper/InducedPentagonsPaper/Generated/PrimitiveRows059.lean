import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData059
import InducedPentagonsPaper.Generated.PrimitiveRows051

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0708 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48825) = [22, 0, 0, 0, 0, 50, 72, 92, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0708_semantics :
    (Generated.hostChunk059[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[0]).mask = 48825 := by decide +kernel
  have hv : (Generated.hostChunk059[0]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 92, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0708]
  rfl

theorem primitive_values_0709 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48826) = [22, 30, 34, 16, 10, 50, 72, 94, 4, 28, 8, 4, 0, 0, 0, 0, 4, 2, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0709_semantics :
    (Generated.hostChunk059[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[1]).mask = 48826 := by decide +kernel
  have hv : (Generated.hostChunk059[1]).primitive.toList = [22, 30, 34, 16, 10, 50, 72, 94, 4, 28, 8, 4, 0, 0, 0, 0, 4, 2, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0709]
  rfl

theorem primitive_values_0710 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48827) = [24, 0, 0, 0, 0, 64, 126, 132, 0, 54, 16, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 16] := by
  decide +kernel

theorem primitive_host_0710_semantics :
    (Generated.hostChunk059[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[2]).mask = 48827 := by decide +kernel
  have hv : (Generated.hostChunk059[2]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 132, 0, 54, 16, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0710]
  rfl

theorem primitive_values_0711 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48828) = [22, 0, 0, 0, 0, 50, 72, 100, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0711_semantics :
    (Generated.hostChunk059[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[3]).mask = 48828 := by decide +kernel
  have hv : (Generated.hostChunk059[3]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 100, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0711]
  rfl

theorem primitive_values_0712 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48829) = [24, 0, 0, 0, 0, 64, 126, 134, 0, 56, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0712_semantics :
    (Generated.hostChunk059[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[4]).mask = 48829 := by decide +kernel
  have hv : (Generated.hostChunk059[4]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 134, 0, 56, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0712]
  rfl

theorem primitive_values_0713 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48830) = [24, 0, 0, 0, 0, 64, 126, 136, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0713_semantics :
    (Generated.hostChunk059[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[5]).mask = 48830 := by decide +kernel
  have hv : (Generated.hostChunk059[5]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 136, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0713]
  rfl

theorem primitive_values_0714 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48831) = [26, 0, 0, 0, 0, 80, 204, 182, 0, 110, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by
  decide +kernel

theorem primitive_host_0714_semantics :
    (Generated.hostChunk059[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[6]).mask = 48831 := by decide +kernel
  have hv : (Generated.hostChunk059[6]).primitive.toList = [26, 0, 0, 0, 0, 80, 204, 182, 0, 110, 32, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0714]
  rfl

theorem primitive_values_0715 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48886) = [24, 0, 0, 0, 0, 66, 138, 144, 0, 62, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0715_semantics :
    (Generated.hostChunk059[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[7]).mask = 48886 := by decide +kernel
  have hv : (Generated.hostChunk059[7]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 144, 0, 62, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0715]
  rfl

theorem primitive_values_0716 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48887) = [26, 0, 0, 0, 0, 82, 210, 192, 0, 130, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_0716_semantics :
    (Generated.hostChunk059[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[8]).mask = 48887 := by decide +kernel
  have hv : (Generated.hostChunk059[8]).primitive.toList = [26, 0, 0, 0, 0, 82, 210, 192, 0, 130, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_0716]
  rfl

theorem primitive_values_0717 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48890) = [24, 20, 26, 16, 12, 64, 126, 134, 8, 58, 20, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0717_semantics :
    (Generated.hostChunk059[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[9]).mask = 48890 := by decide +kernel
  have hv : (Generated.hostChunk059[9]).primitive.toList = [24, 20, 26, 16, 12, 64, 126, 134, 8, 58, 20, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0717]
  rfl

theorem primitive_values_0718 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48891) = [26, 0, 0, 0, 0, 80, 198, 184, 0, 110, 32, 0, 4, 24, 0, 4, 0, 0, 2, 2, 0, 56] := by
  decide +kernel

theorem primitive_host_0718_semantics :
    (Generated.hostChunk059[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[10]).mask = 48891 := by decide +kernel
  have hv : (Generated.hostChunk059[10]).primitive.toList = [26, 0, 0, 0, 0, 80, 198, 184, 0, 110, 32, 0, 4, 24, 0, 4, 0, 0, 2, 2, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0718]
  rfl

theorem primitive_values_0719 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48892) = [24, 10, 14, 12, 0, 62, 108, 132, 0, 42, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0719_semantics :
    (Generated.hostChunk059[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk059[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk059[11]).mask = 48892 := by decide +kernel
  have hv : (Generated.hostChunk059[11]).primitive.toList = [24, 10, 14, 12, 0, 62, 108, 132, 0, 42, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0719]
  rfl

theorem primitive_chunk_059_semantics :
    ∀ h ∈ Generated.hostChunk059.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk059.toList = [Generated.hostChunk059[0], Generated.hostChunk059[1], Generated.hostChunk059[2], Generated.hostChunk059[3], Generated.hostChunk059[4], Generated.hostChunk059[5], Generated.hostChunk059[6], Generated.hostChunk059[7], Generated.hostChunk059[8], Generated.hostChunk059[9], Generated.hostChunk059[10], Generated.hostChunk059[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0708_semantics
  · exact primitive_host_0709_semantics
  · exact primitive_host_0710_semantics
  · exact primitive_host_0711_semantics
  · exact primitive_host_0712_semantics
  · exact primitive_host_0713_semantics
  · exact primitive_host_0714_semantics
  · exact primitive_host_0715_semantics
  · exact primitive_host_0716_semantics
  · exact primitive_host_0717_semantics
  · exact primitive_host_0718_semantics
  · exact primitive_host_0719_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData057
import InducedPentagonsPaper.Generated.PrimitiveRows049

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0684 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48691) = [20, 0, 0, 0, 0, 42, 60, 62, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0684_semantics :
    (Generated.hostChunk057[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[0]).mask = 48691 := by decide +kernel
  have hv : (Generated.hostChunk057[0]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 62, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0684]
  rfl

theorem primitive_values_0685 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48692) = [18, 0, 0, 0, 0, 30, 24, 44, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0685_semantics :
    (Generated.hostChunk057[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[1]).mask = 48692 := by decide +kernel
  have hv : (Generated.hostChunk057[1]).primitive.toList = [18, 0, 0, 0, 0, 30, 24, 44, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0685]
  rfl

theorem primitive_values_0686 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48693) = [20, 0, 0, 0, 0, 40, 48, 60, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0686_semantics :
    (Generated.hostChunk057[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[2]).mask = 48693 := by decide +kernel
  have hv : (Generated.hostChunk057[2]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 60, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0686]
  rfl

theorem primitive_values_0687 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48694) = [20, 0, 0, 0, 0, 42, 60, 70, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0687_semantics :
    (Generated.hostChunk057[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[3]).mask = 48694 := by decide +kernel
  have hv : (Generated.hostChunk057[3]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 70, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0687]
  rfl

theorem primitive_values_0688 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48695) = [22, 0, 0, 0, 0, 54, 102, 96, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0688_semantics :
    (Generated.hostChunk057[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[4]).mask = 48695 := by decide +kernel
  have hv : (Generated.hostChunk057[4]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 96, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0688]
  rfl

theorem primitive_values_0689 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48700) = [20, 0, 0, 0, 0, 40, 48, 68, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0689_semantics :
    (Generated.hostChunk057[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[5]).mask = 48700 := by decide +kernel
  have hv : (Generated.hostChunk057[5]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 68, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0689]
  rfl

theorem primitive_values_0690 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48701) = [22, 0, 0, 0, 0, 52, 90, 92, 0, 34, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0690_semantics :
    (Generated.hostChunk057[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[6]).mask = 48701 := by decide +kernel
  have hv : (Generated.hostChunk057[6]).primitive.toList = [22, 0, 0, 0, 0, 52, 90, 92, 0, 34, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0690]
  rfl

theorem primitive_values_0691 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48702) = [22, 0, 0, 0, 0, 54, 102, 100, 0, 54, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0691_semantics :
    (Generated.hostChunk057[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[7]).mask = 48702 := by decide +kernel
  have hv : (Generated.hostChunk057[7]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 100, 0, 54, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0691]
  rfl

theorem primitive_values_0692 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48703) = [24, 0, 0, 0, 0, 68, 168, 134, 0, 84, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0692_semantics :
    (Generated.hostChunk057[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[8]).mask = 48703 := by decide +kernel
  have hv : (Generated.hostChunk057[8]).primitive.toList = [24, 0, 0, 0, 0, 68, 168, 134, 0, 84, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0692]
  rfl

theorem primitive_values_0693 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48754) = [20, 0, 0, 0, 0, 44, 78, 72, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0693_semantics :
    (Generated.hostChunk057[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[9]).mask = 48754 := by decide +kernel
  have hv : (Generated.hostChunk057[9]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 72, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0693]
  rfl

theorem primitive_values_0694 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48755) = [22, 0, 0, 0, 0, 56, 114, 100, 0, 62, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0694_semantics :
    (Generated.hostChunk057[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[10]).mask = 48755 := by decide +kernel
  have hv : (Generated.hostChunk057[10]).primitive.toList = [22, 0, 0, 0, 0, 56, 114, 100, 0, 62, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0694]
  rfl

theorem primitive_values_0695 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 48756) = [20, 10, 10, 4, 0, 40, 48, 66, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0695_semantics :
    (Generated.hostChunk057[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk057[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk057[11]).mask = 48756 := by decide +kernel
  have hv : (Generated.hostChunk057[11]).primitive.toList = [20, 10, 10, 4, 0, 40, 48, 66, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0695]
  rfl

theorem primitive_chunk_057_semantics :
    ∀ h ∈ Generated.hostChunk057.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk057.toList = [Generated.hostChunk057[0], Generated.hostChunk057[1], Generated.hostChunk057[2], Generated.hostChunk057[3], Generated.hostChunk057[4], Generated.hostChunk057[5], Generated.hostChunk057[6], Generated.hostChunk057[7], Generated.hostChunk057[8], Generated.hostChunk057[9], Generated.hostChunk057[10], Generated.hostChunk057[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0684_semantics
  · exact primitive_host_0685_semantics
  · exact primitive_host_0686_semantics
  · exact primitive_host_0687_semantics
  · exact primitive_host_0688_semantics
  · exact primitive_host_0689_semantics
  · exact primitive_host_0690_semantics
  · exact primitive_host_0691_semantics
  · exact primitive_host_0692_semantics
  · exact primitive_host_0693_semantics
  · exact primitive_host_0694_semantics
  · exact primitive_host_0695_semantics

end InducedPentagons.Paper

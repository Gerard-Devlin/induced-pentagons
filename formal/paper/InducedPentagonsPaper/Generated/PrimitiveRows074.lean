import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData074
import InducedPentagonsPaper.Generated.PrimitiveRows066

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0888 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120575) = [28, 0, 0, 0, 0, 92, 246, 228, 0, 148, 36, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84] := by
  decide +kernel

theorem primitive_host_0888_semantics :
    (Generated.hostChunk074[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[0]).mask = 120575 := by decide +kernel
  have hv : (Generated.hostChunk074[0]).primitive.toList = [28, 0, 0, 0, 0, 92, 246, 228, 0, 148, 36, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84] := by decide +kernel
  rw [hm, hv, primitive_values_0888]
  rfl

theorem primitive_values_0889 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120639) = [26, 0, 0, 0, 0, 78, 192, 180, 0, 96, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0889_semantics :
    (Generated.hostChunk074[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[1]).mask = 120639 := by decide +kernel
  have hv : (Generated.hostChunk074[1]).primitive.toList = [26, 0, 0, 0, 0, 78, 192, 180, 0, 96, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0889]
  rfl

theorem primitive_values_0890 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120699) = [26, 0, 0, 0, 0, 78, 180, 184, 0, 112, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0890_semantics :
    (Generated.hostChunk074[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[2]).mask = 120699 := by decide +kernel
  have hv : (Generated.hostChunk074[2]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 184, 0, 112, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0890]
  rfl

theorem primitive_values_0891 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120700) = [24, 0, 0, 0, 0, 60, 96, 124, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0891_semantics :
    (Generated.hostChunk074[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[3]).mask = 120700 := by decide +kernel
  have hv : (Generated.hostChunk074[3]).primitive.toList = [24, 0, 0, 0, 0, 60, 96, 124, 0, 36, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0891]
  rfl

theorem primitive_values_0892 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120701) = [26, 0, 0, 0, 0, 76, 168, 174, 0, 88, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0892_semantics :
    (Generated.hostChunk074[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[4]).mask = 120701 := by decide +kernel
  have hv : (Generated.hostChunk074[4]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 174, 0, 88, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0892]
  rfl

theorem primitive_values_0893 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120702) = [26, 0, 0, 0, 0, 74, 150, 170, 0, 70, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0893_semantics :
    (Generated.hostChunk074[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[5]).mask = 120702 := by decide +kernel
  have hv : (Generated.hostChunk074[5]).primitive.toList = [26, 0, 0, 0, 0, 74, 150, 170, 0, 70, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0893]
  rfl

theorem primitive_values_0894 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120703) = [28, 0, 0, 0, 0, 92, 246, 230, 0, 150, 40, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 88] := by
  decide +kernel

theorem primitive_host_0894_semantics :
    (Generated.hostChunk074[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[6]).mask = 120703 := by decide +kernel
  have hv : (Generated.hostChunk074[6]).primitive.toList = [28, 0, 0, 0, 0, 92, 246, 230, 0, 150, 40, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 88] := by decide +kernel
  rw [hm, hv, primitive_values_0894]
  rfl

theorem primitive_values_0895 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120830) = [28, 0, 0, 0, 0, 88, 204, 220, 0, 104, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0895_semantics :
    (Generated.hostChunk074[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[7]).mask = 120830 := by decide +kernel
  have hv : (Generated.hostChunk074[7]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 220, 0, 104, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0895]
  rfl

theorem primitive_values_0896 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 120831) = [30, 0, 0, 0, 0, 108, 324, 292, 0, 216, 48, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 144] := by
  decide +kernel

theorem primitive_host_0896_semantics :
    (Generated.hostChunk074[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[8]).mask = 120831 := by decide +kernel
  have hv : (Generated.hostChunk074[8]).primitive.toList = [30, 0, 0, 0, 0, 108, 324, 292, 0, 216, 48, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 144] := by decide +kernel
  rw [hm, hv, primitive_values_0896]
  rfl

theorem primitive_values_0897 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122616) = [24, 30, 42, 24, 0, 60, 96, 126, 0, 42, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0897_semantics :
    (Generated.hostChunk074[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[9]).mask = 122616 := by decide +kernel
  have hv : (Generated.hostChunk074[9]).primitive.toList = [24, 30, 42, 24, 0, 60, 96, 126, 0, 42, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0897]
  rfl

theorem primitive_values_0898 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122617) = [26, 10, 16, 12, 0, 74, 150, 170, 0, 72, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0898_semantics :
    (Generated.hostChunk074[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[10]).mask = 122617 := by decide +kernel
  have hv : (Generated.hostChunk074[10]).primitive.toList = [26, 10, 16, 12, 0, 74, 150, 170, 0, 72, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0898]
  rfl

theorem primitive_values_0899 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122619) = [28, 0, 0, 0, 0, 90, 222, 226, 0, 128, 40, 0, 8, 24, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0899_semantics :
    (Generated.hostChunk074[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk074[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk074[11]).mask = 122619 := by decide +kernel
  have hv : (Generated.hostChunk074[11]).primitive.toList = [28, 0, 0, 0, 0, 90, 222, 226, 0, 128, 40, 0, 8, 24, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0899]
  rfl

theorem primitive_chunk_074_semantics :
    ∀ h ∈ Generated.hostChunk074.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk074.toList = [Generated.hostChunk074[0], Generated.hostChunk074[1], Generated.hostChunk074[2], Generated.hostChunk074[3], Generated.hostChunk074[4], Generated.hostChunk074[5], Generated.hostChunk074[6], Generated.hostChunk074[7], Generated.hostChunk074[8], Generated.hostChunk074[9], Generated.hostChunk074[10], Generated.hostChunk074[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0888_semantics
  · exact primitive_host_0889_semantics
  · exact primitive_host_0890_semantics
  · exact primitive_host_0891_semantics
  · exact primitive_host_0892_semantics
  · exact primitive_host_0893_semantics
  · exact primitive_host_0894_semantics
  · exact primitive_host_0895_semantics
  · exact primitive_host_0896_semantics
  · exact primitive_host_0897_semantics
  · exact primitive_host_0898_semantics
  · exact primitive_host_0899_semantics

end InducedPentagons.Paper

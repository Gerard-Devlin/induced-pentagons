import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData076
import InducedPentagonsPaper.Generated.PrimitiveRows068

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0912 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122878) = [30, 0, 0, 0, 0, 104, 276, 286, 0, 172, 52, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0912_semantics :
    (Generated.hostChunk076[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[0]).mask = 122878 := by decide +kernel
  have hv : (Generated.hostChunk076[0]).primitive.toList = [30, 0, 0, 0, 0, 104, 276, 286, 0, 172, 52, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0912]
  rfl

theorem primitive_values_0913 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 122879) = [32, 0, 0, 0, 0, 124, 396, 366, 0, 292, 52, 0, 0, 168, 0, 0, 0, 0, 0, 0, 4, 220] := by
  decide +kernel

theorem primitive_host_0913_semantics :
    (Generated.hostChunk076[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[1]).mask = 122879 := by decide +kernel
  have hv : (Generated.hostChunk076[1]).primitive.toList = [32, 0, 0, 0, 0, 124, 396, 366, 0, 292, 52, 0, 0, 168, 0, 0, 0, 0, 0, 0, 4, 220] := by decide +kernel
  rw [hm, hv, primitive_values_0913]
  rfl

theorem primitive_values_0914 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128831) = [28, 0, 0, 0, 0, 90, 228, 232, 0, 120, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56] := by
  decide +kernel

theorem primitive_host_0914_semantics :
    (Generated.hostChunk076[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[2]).mask = 128831 := by decide +kernel
  have hv : (Generated.hostChunk076[2]).primitive.toList = [28, 0, 0, 0, 0, 90, 228, 232, 0, 120, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56] := by decide +kernel
  rw [hm, hv, primitive_values_0914]
  rfl

theorem primitive_values_0915 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128891) = [28, 0, 0, 0, 0, 92, 234, 240, 0, 156, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0915_semantics :
    (Generated.hostChunk076[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[3]).mask = 128891 := by decide +kernel
  have hv : (Generated.hostChunk076[3]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 240, 0, 156, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0915]
  rfl

theorem primitive_values_0916 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128892) = [26, 0, 0, 0, 0, 72, 132, 168, 0, 54, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0916_semantics :
    (Generated.hostChunk076[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[4]).mask = 128892 := by decide +kernel
  have hv : (Generated.hostChunk076[4]).primitive.toList = [26, 0, 0, 0, 0, 72, 132, 168, 0, 54, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0916]
  rfl

theorem primitive_values_0917 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128893) = [28, 0, 0, 0, 0, 88, 204, 224, 0, 110, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0917_semantics :
    (Generated.hostChunk076[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[5]).mask = 128893 := by decide +kernel
  have hv : (Generated.hostChunk076[5]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 224, 0, 110, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0917]
  rfl

theorem primitive_values_0918 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128895) = [30, 0, 0, 0, 0, 106, 300, 292, 0, 198, 56, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 128] := by
  decide +kernel

theorem primitive_host_0918_semantics :
    (Generated.hostChunk076[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[6]).mask = 128895 := by decide +kernel
  have hv : (Generated.hostChunk076[6]).primitive.toList = [30, 0, 0, 0, 0, 106, 300, 292, 0, 198, 56, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 128] := by decide +kernel
  rw [hm, hv, primitive_values_0918]
  rfl

theorem primitive_values_0919 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128956) = [26, 0, 0, 0, 0, 72, 132, 176, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0919_semantics :
    (Generated.hostChunk076[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[7]).mask = 128956 := by decide +kernel
  have hv : (Generated.hostChunk076[7]).primitive.toList = [26, 0, 0, 0, 0, 72, 132, 176, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0919]
  rfl

theorem primitive_values_0920 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128957) = [28, 0, 0, 0, 0, 88, 204, 228, 0, 118, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0920_semantics :
    (Generated.hostChunk076[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[8]).mask = 128957 := by decide +kernel
  have hv : (Generated.hostChunk076[8]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 228, 0, 118, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0920]
  rfl

theorem primitive_values_0921 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128958) = [28, 0, 0, 0, 0, 86, 186, 220, 0, 92, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0921_semantics :
    (Generated.hostChunk076[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[9]).mask = 128958 := by decide +kernel
  have hv : (Generated.hostChunk076[9]).primitive.toList = [28, 0, 0, 0, 0, 86, 186, 220, 0, 92, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0921]
  rfl

theorem primitive_values_0922 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 128959) = [30, 0, 0, 0, 0, 104, 282, 286, 0, 176, 56, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 104] := by
  decide +kernel

theorem primitive_host_0922_semantics :
    (Generated.hostChunk076[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[10]).mask = 128959 := by decide +kernel
  have hv : (Generated.hostChunk076[10]).primitive.toList = [30, 0, 0, 0, 0, 104, 282, 286, 0, 176, 56, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 104] := by decide +kernel
  rw [hm, hv, primitive_values_0922]
  rfl

theorem primitive_values_0923 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 129022) = [30, 0, 0, 0, 0, 102, 258, 280, 0, 148, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0923_semantics :
    (Generated.hostChunk076[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk076[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk076[11]).mask = 129022 := by decide +kernel
  have hv : (Generated.hostChunk076[11]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 280, 0, 148, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0923]
  rfl

theorem primitive_chunk_076_semantics :
    ∀ h ∈ Generated.hostChunk076.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk076.toList = [Generated.hostChunk076[0], Generated.hostChunk076[1], Generated.hostChunk076[2], Generated.hostChunk076[3], Generated.hostChunk076[4], Generated.hostChunk076[5], Generated.hostChunk076[6], Generated.hostChunk076[7], Generated.hostChunk076[8], Generated.hostChunk076[9], Generated.hostChunk076[10], Generated.hostChunk076[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0912_semantics
  · exact primitive_host_0913_semantics
  · exact primitive_host_0914_semantics
  · exact primitive_host_0915_semantics
  · exact primitive_host_0916_semantics
  · exact primitive_host_0917_semantics
  · exact primitive_host_0918_semantics
  · exact primitive_host_0919_semantics
  · exact primitive_host_0920_semantics
  · exact primitive_host_0921_semantics
  · exact primitive_host_0922_semantics
  · exact primitive_host_0923_semantics

end InducedPentagons.Paper

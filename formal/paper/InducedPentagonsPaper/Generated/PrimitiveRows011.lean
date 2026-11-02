import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData011
import InducedPentagonsPaper.Generated.PrimitiveRows003

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0132 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2847) = [16, 0, 0, 0, 0, 34, 66, 40, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0132_semantics :
    (Generated.hostChunk011[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[0]).mask = 2847 := by decide +kernel
  have hv : (Generated.hostChunk011[0]).primitive.toList = [16, 0, 0, 0, 0, 34, 66, 40, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0132]
  rfl

theorem primitive_values_0133 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2856) = [10, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0133_semantics :
    (Generated.hostChunk011[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[1]).mask = 2856 := by decide +kernel
  have hv : (Generated.hostChunk011[1]).primitive.toList = [10, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0133]
  rfl

theorem primitive_values_0134 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2857) = [12, 0, 0, 0, 0, 14, 12, 10, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0134_semantics :
    (Generated.hostChunk011[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[2]).mask = 2857 := by decide +kernel
  have hv : (Generated.hostChunk011[2]).primitive.toList = [12, 0, 0, 0, 0, 14, 12, 10, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0134]
  rfl

theorem primitive_values_0135 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2858) = [12, 0, 0, 0, 0, 12, 6, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0135_semantics :
    (Generated.hostChunk011[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[3]).mask = 2858 := by decide +kernel
  have hv : (Generated.hostChunk011[3]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0135]
  rfl

theorem primitive_values_0136 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2859) = [14, 0, 0, 0, 0, 22, 30, 22, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0136_semantics :
    (Generated.hostChunk011[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[4]).mask = 2859 := by decide +kernel
  have hv : (Generated.hostChunk011[4]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 22, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0136]
  rfl

theorem primitive_values_0137 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2862) = [14, 0, 0, 0, 0, 20, 24, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0137_semantics :
    (Generated.hostChunk011[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[5]).mask = 2862 := by decide +kernel
  have hv : (Generated.hostChunk011[5]).primitive.toList = [14, 0, 0, 0, 0, 20, 24, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0137]
  rfl

theorem primitive_values_0138 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2863) = [16, 0, 0, 0, 0, 32, 66, 34, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0138_semantics :
    (Generated.hostChunk011[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[6]).mask = 2863 := by decide +kernel
  have hv : (Generated.hostChunk011[6]).primitive.toList = [16, 0, 0, 0, 0, 32, 66, 34, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0138]
  rfl

theorem primitive_values_0139 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2872) = [12, 0, 0, 0, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0139_semantics :
    (Generated.hostChunk011[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[7]).mask = 2872 := by decide +kernel
  have hv : (Generated.hostChunk011[7]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0139]
  rfl

theorem primitive_values_0140 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2873) = [14, 0, 0, 0, 0, 22, 30, 20, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0140_semantics :
    (Generated.hostChunk011[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[8]).mask = 2873 := by decide +kernel
  have hv : (Generated.hostChunk011[8]).primitive.toList = [14, 0, 0, 0, 0, 22, 30, 20, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0140]
  rfl

theorem primitive_values_0141 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2874) = [14, 0, 0, 0, 0, 20, 24, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0141_semantics :
    (Generated.hostChunk011[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[9]).mask = 2874 := by decide +kernel
  have hv : (Generated.hostChunk011[9]).primitive.toList = [14, 0, 0, 0, 0, 20, 24, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0141]
  rfl

theorem primitive_values_0142 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2875) = [16, 0, 0, 0, 0, 32, 66, 36, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0142_semantics :
    (Generated.hostChunk011[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[10]).mask = 2875 := by decide +kernel
  have hv : (Generated.hostChunk011[10]).primitive.toList = [16, 0, 0, 0, 0, 32, 66, 36, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0142]
  rfl

theorem primitive_values_0143 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2878) = [16, 0, 0, 0, 0, 30, 60, 32, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0143_semantics :
    (Generated.hostChunk011[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk011[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk011[11]).mask = 2878 := by decide +kernel
  have hv : (Generated.hostChunk011[11]).primitive.toList = [16, 0, 0, 0, 0, 30, 60, 32, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0143]
  rfl

theorem primitive_chunk_011_semantics :
    ∀ h ∈ Generated.hostChunk011.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk011.toList = [Generated.hostChunk011[0], Generated.hostChunk011[1], Generated.hostChunk011[2], Generated.hostChunk011[3], Generated.hostChunk011[4], Generated.hostChunk011[5], Generated.hostChunk011[6], Generated.hostChunk011[7], Generated.hostChunk011[8], Generated.hostChunk011[9], Generated.hostChunk011[10], Generated.hostChunk011[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0132_semantics
  · exact primitive_host_0133_semantics
  · exact primitive_host_0134_semantics
  · exact primitive_host_0135_semantics
  · exact primitive_host_0136_semantics
  · exact primitive_host_0137_semantics
  · exact primitive_host_0138_semantics
  · exact primitive_host_0139_semantics
  · exact primitive_host_0140_semantics
  · exact primitive_host_0141_semantics
  · exact primitive_host_0142_semantics
  · exact primitive_host_0143_semantics

end InducedPentagons.Paper

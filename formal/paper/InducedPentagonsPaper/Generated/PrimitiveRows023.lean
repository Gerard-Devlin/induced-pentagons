import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData023
import InducedPentagonsPaper.Generated.PrimitiveRows015

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0276 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7135) = [22, 0, 0, 0, 0, 66, 156, 136, 0, 104, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0276_semantics :
    (Generated.hostChunk023[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[0]).mask = 7135 := by decide +kernel
  have hv : (Generated.hostChunk023[0]).primitive.toList = [22, 0, 0, 0, 0, 66, 156, 136, 0, 104, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0276]
  rfl

theorem primitive_values_0277 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7150) = [20, 0, 0, 0, 0, 48, 84, 84, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0277_semantics :
    (Generated.hostChunk023[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[1]).mask = 7150 := by decide +kernel
  have hv : (Generated.hostChunk023[1]).primitive.toList = [20, 0, 0, 0, 0, 48, 84, 84, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0277]
  rfl

theorem primitive_values_0278 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7151) = [22, 0, 0, 0, 0, 64, 156, 126, 0, 92, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0278_semantics :
    (Generated.hostChunk023[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[2]).mask = 7151 := by decide +kernel
  have hv : (Generated.hostChunk023[2]).primitive.toList = [22, 0, 0, 0, 0, 64, 156, 126, 0, 92, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0278]
  rfl

theorem primitive_values_0279 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7152) = [16, 0, 0, 0, 0, 26, 30, 28, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0279_semantics :
    (Generated.hostChunk023[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[3]).mask = 7152 := by decide +kernel
  have hv : (Generated.hostChunk023[3]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 28, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0279]
  rfl

theorem primitive_values_0280 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7153) = [18, 0, 0, 0, 0, 38, 72, 50, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0280_semantics :
    (Generated.hostChunk023[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[4]).mask = 7153 := by decide +kernel
  have hv : (Generated.hostChunk023[4]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 50, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0280]
  rfl

theorem primitive_values_0281 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7154) = [18, 0, 0, 0, 0, 36, 54, 52, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0281_semantics :
    (Generated.hostChunk023[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[5]).mask = 7154 := by decide +kernel
  have hv : (Generated.hostChunk023[5]).primitive.toList = [18, 0, 0, 0, 0, 36, 54, 52, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0281]
  rfl

theorem primitive_values_0282 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7155) = [20, 0, 0, 0, 0, 50, 108, 84, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0282_semantics :
    (Generated.hostChunk023[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[6]).mask = 7155 := by decide +kernel
  have hv : (Generated.hostChunk023[6]).primitive.toList = [20, 0, 0, 0, 0, 50, 108, 84, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0282]
  rfl

theorem primitive_values_0283 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7156) = [18, 0, 0, 0, 0, 34, 42, 48, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0283_semantics :
    (Generated.hostChunk023[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[7]).mask = 7156 := by decide +kernel
  have hv : (Generated.hostChunk023[7]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 48, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0283]
  rfl

theorem primitive_values_0284 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7157) = [20, 0, 0, 0, 0, 48, 96, 78, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0284_semantics :
    (Generated.hostChunk023[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[8]).mask = 7157 := by decide +kernel
  have hv : (Generated.hostChunk023[8]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 78, 0, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0284]
  rfl

theorem primitive_values_0285 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7158) = [20, 0, 0, 0, 0, 46, 78, 78, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0285_semantics :
    (Generated.hostChunk023[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[9]).mask = 7158 := by decide +kernel
  have hv : (Generated.hostChunk023[9]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 78, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0285]
  rfl

theorem primitive_values_0286 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7159) = [22, 0, 0, 0, 0, 62, 150, 118, 0, 76, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0286_semantics :
    (Generated.hostChunk023[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[10]).mask = 7159 := by decide +kernel
  have hv : (Generated.hostChunk023[10]).primitive.toList = [22, 0, 0, 0, 0, 62, 150, 118, 0, 76, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0286]
  rfl

theorem primitive_values_0287 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7164) = [20, 0, 0, 0, 0, 44, 66, 76, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0287_semantics :
    (Generated.hostChunk023[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk023[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk023[11]).mask = 7164 := by decide +kernel
  have hv : (Generated.hostChunk023[11]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 76, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0287]
  rfl

theorem primitive_chunk_023_semantics :
    ∀ h ∈ Generated.hostChunk023.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk023.toList = [Generated.hostChunk023[0], Generated.hostChunk023[1], Generated.hostChunk023[2], Generated.hostChunk023[3], Generated.hostChunk023[4], Generated.hostChunk023[5], Generated.hostChunk023[6], Generated.hostChunk023[7], Generated.hostChunk023[8], Generated.hostChunk023[9], Generated.hostChunk023[10], Generated.hostChunk023[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0276_semantics
  · exact primitive_host_0277_semantics
  · exact primitive_host_0278_semantics
  · exact primitive_host_0279_semantics
  · exact primitive_host_0280_semantics
  · exact primitive_host_0281_semantics
  · exact primitive_host_0282_semantics
  · exact primitive_host_0283_semantics
  · exact primitive_host_0284_semantics
  · exact primitive_host_0285_semantics
  · exact primitive_host_0286_semantics
  · exact primitive_host_0287_semantics

end InducedPentagons.Paper

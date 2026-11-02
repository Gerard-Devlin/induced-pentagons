import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData021
import InducedPentagonsPaper.Generated.PrimitiveRows013

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0252 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6908) = [18, 10, 8, 4, 0, 34, 42, 50, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0252_semantics :
    (Generated.hostChunk021[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[0]).mask = 6908 := by decide +kernel
  have hv : (Generated.hostChunk021[0]).primitive.toList = [18, 10, 8, 4, 0, 34, 42, 50, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0252]
  rfl

theorem primitive_values_0253 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6909) = [20, 0, 0, 0, 0, 48, 96, 80, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0253_semantics :
    (Generated.hostChunk021[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[1]).mask = 6909 := by decide +kernel
  have hv : (Generated.hostChunk021[1]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 80, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0253]
  rfl

theorem primitive_values_0254 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6911) = [22, 0, 0, 0, 0, 64, 174, 118, 0, 78, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0254_semantics :
    (Generated.hostChunk021[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[2]).mask = 6911 := by decide +kernel
  have hv : (Generated.hostChunk021[2]).primitive.toList = [22, 0, 0, 0, 0, 64, 174, 118, 0, 78, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0254]
  rfl

theorem primitive_values_0255 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7068) = [16, 0, 0, 0, 0, 28, 24, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0255_semantics :
    (Generated.hostChunk021[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[3]).mask = 7068 := by decide +kernel
  have hv : (Generated.hostChunk021[3]).primitive.toList = [16, 0, 0, 0, 0, 28, 24, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0255]
  rfl

theorem primitive_values_0256 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7069) = [18, 0, 0, 0, 0, 40, 60, 68, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0256_semantics :
    (Generated.hostChunk021[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[4]).mask = 7069 := by decide +kernel
  have hv : (Generated.hostChunk021[4]).primitive.toList = [18, 0, 0, 0, 0, 40, 60, 68, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0256]
  rfl

theorem primitive_values_0257 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7070) = [18, 0, 0, 0, 0, 38, 48, 66, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0257_semantics :
    (Generated.hostChunk021[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[5]).mask = 7070 := by decide +kernel
  have hv : (Generated.hostChunk021[5]).primitive.toList = [18, 0, 0, 0, 0, 38, 48, 66, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0257]
  rfl

theorem primitive_values_0258 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7071) = [20, 0, 0, 0, 0, 52, 102, 96, 0, 54, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0258_semantics :
    (Generated.hostChunk021[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[6]).mask = 7071 := by decide +kernel
  have hv : (Generated.hostChunk021[6]).primitive.toList = [20, 0, 0, 0, 0, 52, 102, 96, 0, 54, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0258]
  rfl

theorem primitive_values_0259 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7084) = [16, 0, 0, 0, 0, 26, 24, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0259_semantics :
    (Generated.hostChunk021[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[7]).mask = 7084 := by decide +kernel
  have hv : (Generated.hostChunk021[7]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0259]
  rfl

theorem primitive_values_0260 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7085) = [18, 0, 0, 0, 0, 38, 60, 62, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0260_semantics :
    (Generated.hostChunk021[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[8]).mask = 7085 := by decide +kernel
  have hv : (Generated.hostChunk021[8]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 62, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0260]
  rfl

theorem primitive_values_0261 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7086) = [18, 0, 0, 0, 0, 36, 48, 56, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0261_semantics :
    (Generated.hostChunk021[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[9]).mask = 7086 := by decide +kernel
  have hv : (Generated.hostChunk021[9]).primitive.toList = [18, 0, 0, 0, 0, 36, 48, 56, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0261]
  rfl

theorem primitive_values_0262 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7087) = [20, 0, 0, 0, 0, 50, 102, 88, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0262_semantics :
    (Generated.hostChunk021[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[10]).mask = 7087 := by decide +kernel
  have hv : (Generated.hostChunk021[10]).primitive.toList = [20, 0, 0, 0, 0, 50, 102, 88, 0, 44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0262]
  rfl

theorem primitive_values_0263 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7088) = [14, 0, 0, 0, 0, 16, 6, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0263_semantics :
    (Generated.hostChunk021[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk021[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk021[11]).mask = 7088 := by decide +kernel
  have hv : (Generated.hostChunk021[11]).primitive.toList = [14, 0, 0, 0, 0, 16, 6, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0263]
  rfl

theorem primitive_chunk_021_semantics :
    ∀ h ∈ Generated.hostChunk021.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk021.toList = [Generated.hostChunk021[0], Generated.hostChunk021[1], Generated.hostChunk021[2], Generated.hostChunk021[3], Generated.hostChunk021[4], Generated.hostChunk021[5], Generated.hostChunk021[6], Generated.hostChunk021[7], Generated.hostChunk021[8], Generated.hostChunk021[9], Generated.hostChunk021[10], Generated.hostChunk021[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0252_semantics
  · exact primitive_host_0253_semantics
  · exact primitive_host_0254_semantics
  · exact primitive_host_0255_semantics
  · exact primitive_host_0256_semantics
  · exact primitive_host_0257_semantics
  · exact primitive_host_0258_semantics
  · exact primitive_host_0259_semantics
  · exact primitive_host_0260_semantics
  · exact primitive_host_0261_semantics
  · exact primitive_host_0262_semantics
  · exact primitive_host_0263_semantics

end InducedPentagons.Paper

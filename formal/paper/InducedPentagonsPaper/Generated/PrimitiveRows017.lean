import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData017
import InducedPentagonsPaper.Generated.PrimitiveRows009

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0204 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6621) = [18, 0, 0, 0, 0, 42, 66, 70, 0, 36, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0204_semantics :
    (Generated.hostChunk017[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[0]).mask = 6621 := by decide +kernel
  have hv : (Generated.hostChunk017[0]).primitive.toList = [18, 0, 0, 0, 0, 42, 66, 70, 0, 36, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0204]
  rfl

theorem primitive_values_0205 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6623) = [20, 0, 0, 0, 0, 56, 120, 104, 0, 82, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0205_semantics :
    (Generated.hostChunk017[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[1]).mask = 6623 := by decide +kernel
  have hv : (Generated.hostChunk017[1]).primitive.toList = [20, 0, 0, 0, 0, 56, 120, 104, 0, 82, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0205]
  rfl

theorem primitive_values_0206 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6640) = [14, 0, 0, 0, 0, 18, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0206_semantics :
    (Generated.hostChunk017[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[2]).mask = 6640 := by decide +kernel
  have hv : (Generated.hostChunk017[2]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0206]
  rfl

theorem primitive_values_0207 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6641) = [16, 0, 0, 0, 0, 28, 36, 32, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0207_semantics :
    (Generated.hostChunk017[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[3]).mask = 6641 := by decide +kernel
  have hv : (Generated.hostChunk017[3]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 32, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0207]
  rfl

theorem primitive_values_0208 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6643) = [18, 0, 0, 0, 0, 40, 72, 60, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0208_semantics :
    (Generated.hostChunk017[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[4]).mask = 6643 := by decide +kernel
  have hv : (Generated.hostChunk017[4]).primitive.toList = [18, 0, 0, 0, 0, 40, 72, 60, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0208]
  rfl

theorem primitive_values_0209 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6644) = [16, 0, 0, 0, 0, 26, 24, 28, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0209_semantics :
    (Generated.hostChunk017[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[5]).mask = 6644 := by decide +kernel
  have hv : (Generated.hostChunk017[5]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 28, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0209]
  rfl

theorem primitive_values_0210 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6645) = [18, 0, 0, 0, 0, 38, 60, 54, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0210_semantics :
    (Generated.hostChunk017[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[6]).mask = 6645 := by decide +kernel
  have hv : (Generated.hostChunk017[6]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 54, 0, 24, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0210]
  rfl

theorem primitive_values_0211 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6647) = [20, 0, 0, 0, 0, 52, 114, 88, 0, 56, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0211_semantics :
    (Generated.hostChunk017[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[7]).mask = 6647 := by decide +kernel
  have hv : (Generated.hostChunk017[7]).primitive.toList = [20, 0, 0, 0, 0, 52, 114, 88, 0, 56, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0211]
  rfl

theorem primitive_values_0212 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6652) = [18, 0, 0, 0, 0, 36, 48, 52, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0212_semantics :
    (Generated.hostChunk017[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[8]).mask = 6652 := by decide +kernel
  have hv : (Generated.hostChunk017[8]).primitive.toList = [18, 0, 0, 0, 0, 36, 48, 52, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0212]
  rfl

theorem primitive_values_0213 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6653) = [20, 0, 0, 0, 0, 50, 102, 84, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0213_semantics :
    (Generated.hostChunk017[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[9]).mask = 6653 := by decide +kernel
  have hv : (Generated.hostChunk017[9]).primitive.toList = [20, 0, 0, 0, 0, 50, 102, 84, 0, 40, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0213]
  rfl

theorem primitive_values_0214 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6655) = [22, 0, 0, 0, 0, 66, 180, 124, 0, 92, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0214_semantics :
    (Generated.hostChunk017[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[10]).mask = 6655 := by decide +kernel
  have hv : (Generated.hostChunk017[10]).primitive.toList = [22, 0, 0, 0, 0, 66, 180, 124, 0, 92, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0214]
  rfl

theorem primitive_values_0215 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6808) = [12, 0, 0, 0, 0, 12, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0215_semantics :
    (Generated.hostChunk017[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk017[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk017[11]).mask = 6808 := by decide +kernel
  have hv : (Generated.hostChunk017[11]).primitive.toList = [12, 0, 0, 0, 0, 12, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0215]
  rfl

theorem primitive_chunk_017_semantics :
    ∀ h ∈ Generated.hostChunk017.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk017.toList = [Generated.hostChunk017[0], Generated.hostChunk017[1], Generated.hostChunk017[2], Generated.hostChunk017[3], Generated.hostChunk017[4], Generated.hostChunk017[5], Generated.hostChunk017[6], Generated.hostChunk017[7], Generated.hostChunk017[8], Generated.hostChunk017[9], Generated.hostChunk017[10], Generated.hostChunk017[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0204_semantics
  · exact primitive_host_0205_semantics
  · exact primitive_host_0206_semantics
  · exact primitive_host_0207_semantics
  · exact primitive_host_0208_semantics
  · exact primitive_host_0209_semantics
  · exact primitive_host_0210_semantics
  · exact primitive_host_0211_semantics
  · exact primitive_host_0212_semantics
  · exact primitive_host_0213_semantics
  · exact primitive_host_0214_semantics
  · exact primitive_host_0215_semantics

end InducedPentagons.Paper

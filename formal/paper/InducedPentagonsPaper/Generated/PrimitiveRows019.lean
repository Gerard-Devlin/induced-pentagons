import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData019
import InducedPentagonsPaper.Generated.PrimitiveRows011

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0228 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6828) = [14, 0, 0, 0, 0, 18, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0228_semantics :
    (Generated.hostChunk019[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[0]).mask = 6828 := by decide +kernel
  have hv : (Generated.hostChunk019[0]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0228]
  rfl

theorem primitive_values_0229 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6829) = [16, 0, 0, 0, 0, 28, 36, 38, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0229_semantics :
    (Generated.hostChunk019[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[1]).mask = 6829 := by decide +kernel
  have hv : (Generated.hostChunk019[1]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 38, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0229]
  rfl

theorem primitive_values_0230 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6830) = [16, 0, 0, 0, 0, 28, 36, 34, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0230_semantics :
    (Generated.hostChunk019[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[2]).mask = 6830 := by decide +kernel
  have hv : (Generated.hostChunk019[2]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 34, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0230]
  rfl

theorem primitive_values_0231 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6831) = [18, 0, 0, 0, 0, 40, 78, 58, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0231_semantics :
    (Generated.hostChunk019[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[3]).mask = 6831 := by decide +kernel
  have hv : (Generated.hostChunk019[3]).primitive.toList = [18, 0, 0, 0, 0, 40, 78, 58, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0231]
  rfl

theorem primitive_values_0232 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6840) = [14, 0, 0, 0, 0, 16, 6, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0232_semantics :
    (Generated.hostChunk019[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[4]).mask = 6840 := by decide +kernel
  have hv : (Generated.hostChunk019[4]).primitive.toList = [14, 0, 0, 0, 0, 16, 6, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0232]
  rfl

theorem primitive_values_0233 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6841) = [16, 10, 6, 4, 0, 26, 30, 30, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0233_semantics :
    (Generated.hostChunk019[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[5]).mask = 6841 := by decide +kernel
  have hv : (Generated.hostChunk019[5]).primitive.toList = [16, 10, 6, 4, 0, 26, 30, 30, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0233]
  rfl

theorem primitive_values_0234 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6843) = [18, 0, 0, 0, 0, 38, 72, 52, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0234_semantics :
    (Generated.hostChunk019[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[6]).mask = 6843 := by decide +kernel
  have hv : (Generated.hostChunk019[6]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 52, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0234]
  rfl

theorem primitive_values_0235 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6844) = [16, 0, 0, 0, 0, 26, 30, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0235_semantics :
    (Generated.hostChunk019[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[7]).mask = 6844 := by decide +kernel
  have hv : (Generated.hostChunk019[7]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0235]
  rfl

theorem primitive_values_0236 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6845) = [18, 0, 0, 0, 0, 38, 72, 54, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0236_semantics :
    (Generated.hostChunk019[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[8]).mask = 6845 := by decide +kernel
  have hv : (Generated.hostChunk019[8]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 54, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0236]
  rfl

theorem primitive_values_0237 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6847) = [20, 0, 0, 0, 0, 52, 138, 80, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0237_semantics :
    (Generated.hostChunk019[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[9]).mask = 6847 := by decide +kernel
  have hv : (Generated.hostChunk019[9]).primitive.toList = [20, 0, 0, 0, 0, 52, 138, 80, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0237]
  rfl

theorem primitive_values_0238 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6875) = [18, 0, 0, 0, 0, 42, 72, 66, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0238_semantics :
    (Generated.hostChunk019[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[10]).mask = 6875 := by decide +kernel
  have hv : (Generated.hostChunk019[10]).primitive.toList = [18, 0, 0, 0, 0, 42, 72, 66, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0238]
  rfl

theorem primitive_values_0239 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 6876) = [16, 10, 6, 0, 0, 28, 24, 42, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0239_semantics :
    (Generated.hostChunk019[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk019[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk019[11]).mask = 6876 := by decide +kernel
  have hv : (Generated.hostChunk019[11]).primitive.toList = [16, 10, 6, 0, 0, 28, 24, 42, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0239]
  rfl

theorem primitive_chunk_019_semantics :
    ∀ h ∈ Generated.hostChunk019.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk019.toList = [Generated.hostChunk019[0], Generated.hostChunk019[1], Generated.hostChunk019[2], Generated.hostChunk019[3], Generated.hostChunk019[4], Generated.hostChunk019[5], Generated.hostChunk019[6], Generated.hostChunk019[7], Generated.hostChunk019[8], Generated.hostChunk019[9], Generated.hostChunk019[10], Generated.hostChunk019[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0228_semantics
  · exact primitive_host_0229_semantics
  · exact primitive_host_0230_semantics
  · exact primitive_host_0231_semantics
  · exact primitive_host_0232_semantics
  · exact primitive_host_0233_semantics
  · exact primitive_host_0234_semantics
  · exact primitive_host_0235_semantics
  · exact primitive_host_0236_semantics
  · exact primitive_host_0237_semantics
  · exact primitive_host_0238_semantics
  · exact primitive_host_0239_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData071
import InducedPentagonsPaper.Generated.PrimitiveRows063

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0852 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114044) = [24, 20, 26, 20, 12, 62, 108, 130, 8, 54, 20, 8, 0, 0, 0, 0, 8, 2, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0852_semantics :
    (Generated.hostChunk071[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[0]).mask = 114044 := by decide +kernel
  have hv : (Generated.hostChunk071[0]).primitive.toList = [24, 20, 26, 20, 12, 62, 108, 130, 8, 54, 20, 8, 0, 0, 0, 0, 8, 2, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0852]
  rfl

theorem primitive_values_0853 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114045) = [26, 0, 0, 0, 0, 76, 162, 174, 0, 84, 32, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 32] := by
  decide +kernel

theorem primitive_host_0853_semantics :
    (Generated.hostChunk071[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[1]).mask = 114045 := by decide +kernel
  have hv : (Generated.hostChunk071[1]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 174, 0, 84, 32, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0853]
  rfl

theorem primitive_values_0854 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114046) = [26, 0, 0, 0, 0, 78, 180, 182, 0, 110, 20, 0, 4, 48, 0, 4, 0, 0, 1, 1, 0, 68] := by
  decide +kernel

theorem primitive_host_0854_semantics :
    (Generated.hostChunk071[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[2]).mask = 114046 := by decide +kernel
  have hv : (Generated.hostChunk071[2]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 182, 0, 110, 20, 0, 4, 48, 0, 4, 0, 0, 1, 1, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0854]
  rfl

theorem primitive_values_0855 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114047) = [28, 0, 0, 0, 0, 94, 258, 236, 0, 168, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 2, 108] := by
  decide +kernel

theorem primitive_host_0855_semantics :
    (Generated.hostChunk071[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[3]).mask = 114047 := by decide +kernel
  have hv : (Generated.hostChunk071[3]).primitive.toList = [28, 0, 0, 0, 0, 94, 258, 236, 0, 168, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 2, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0855]
  rfl

theorem primitive_values_0856 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114159) = [28, 0, 0, 0, 0, 96, 264, 248, 0, 192, 24, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 144] := by
  decide +kernel

theorem primitive_host_0856_semantics :
    (Generated.hostChunk071[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[4]).mask = 114159 := by decide +kernel
  have hv : (Generated.hostChunk071[4]).primitive.toList = [28, 0, 0, 0, 0, 96, 264, 248, 0, 192, 24, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 144] := by decide +kernel
  rw [hm, hv, primitive_values_0856]
  rfl

theorem primitive_values_0857 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114166) = [26, 0, 0, 0, 0, 78, 180, 180, 0, 108, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0857_semantics :
    (Generated.hostChunk071[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[5]).mask = 114166 := by decide +kernel
  have hv : (Generated.hostChunk071[5]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 180, 0, 108, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0857]
  rfl

theorem primitive_values_0858 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114167) = [28, 0, 0, 0, 0, 94, 252, 238, 0, 168, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0858_semantics :
    (Generated.hostChunk071[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[6]).mask = 114167 := by decide +kernel
  have hv : (Generated.hostChunk071[6]).primitive.toList = [28, 0, 0, 0, 0, 94, 252, 238, 0, 168, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0858]
  rfl

theorem primitive_values_0859 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114168) = [24, 20, 24, 16, 24, 62, 108, 132, 16, 58, 8, 0, 0, 24, 8, 0, 16, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0859_semantics :
    (Generated.hostChunk071[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[7]).mask = 114168 := by decide +kernel
  have hv : (Generated.hostChunk071[7]).primitive.toList = [24, 20, 24, 16, 24, 62, 108, 132, 16, 58, 8, 0, 0, 24, 8, 0, 16, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0859]
  rfl

theorem primitive_values_0860 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114169) = [26, 0, 0, 0, 0, 76, 162, 176, 0, 88, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0860_semantics :
    (Generated.hostChunk071[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[8]).mask = 114169 := by decide +kernel
  have hv : (Generated.hostChunk071[8]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 176, 0, 88, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0860]
  rfl

theorem primitive_values_0861 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114170) = [26, 10, 14, 12, 14, 76, 162, 178, 12, 92, 24, 0, 0, 24, 4, 0, 12, 2, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0861_semantics :
    (Generated.hostChunk071[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[9]).mask = 114170 := by decide +kernel
  have hv : (Generated.hostChunk071[9]).primitive.toList = [26, 10, 14, 12, 14, 76, 162, 178, 12, 92, 24, 0, 0, 24, 4, 0, 12, 2, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0861]
  rfl

theorem primitive_values_0862 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114171) = [28, 0, 0, 0, 0, 92, 234, 234, 0, 148, 40, 0, 0, 48, 0, 4, 0, 0, 1, 1, 0, 88] := by
  decide +kernel

theorem primitive_host_0862_semantics :
    (Generated.hostChunk071[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[10]).mask = 114171 := by decide +kernel
  have hv : (Generated.hostChunk071[10]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 234, 0, 148, 40, 0, 0, 48, 0, 4, 0, 0, 1, 1, 0, 88] := by decide +kernel
  rw [hm, hv, primitive_values_0862]
  rfl

theorem primitive_values_0863 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 114174) = [28, 0, 0, 0, 0, 92, 234, 236, 0, 152, 28, 0, 0, 72, 0, 8, 0, 0, 2, 2, 0, 100] := by
  decide +kernel

theorem primitive_host_0863_semantics :
    (Generated.hostChunk071[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk071[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk071[11]).mask = 114174 := by decide +kernel
  have hv : (Generated.hostChunk071[11]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 236, 0, 152, 28, 0, 0, 72, 0, 8, 0, 0, 2, 2, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0863]
  rfl

theorem primitive_chunk_071_semantics :
    ∀ h ∈ Generated.hostChunk071.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk071.toList = [Generated.hostChunk071[0], Generated.hostChunk071[1], Generated.hostChunk071[2], Generated.hostChunk071[3], Generated.hostChunk071[4], Generated.hostChunk071[5], Generated.hostChunk071[6], Generated.hostChunk071[7], Generated.hostChunk071[8], Generated.hostChunk071[9], Generated.hostChunk071[10], Generated.hostChunk071[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0852_semantics
  · exact primitive_host_0853_semantics
  · exact primitive_host_0854_semantics
  · exact primitive_host_0855_semantics
  · exact primitive_host_0856_semantics
  · exact primitive_host_0857_semantics
  · exact primitive_host_0858_semantics
  · exact primitive_host_0859_semantics
  · exact primitive_host_0860_semantics
  · exact primitive_host_0861_semantics
  · exact primitive_host_0862_semantics
  · exact primitive_host_0863_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData083
import InducedPentagonsPaper.Generated.PrimitiveRows075

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0996 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380796) = [26, 0, 0, 0, 0, 72, 132, 164, 0, 68, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0996_semantics :
    (Generated.hostChunk083[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[0]).mask = 380796 := by decide +kernel
  have hv : (Generated.hostChunk083[0]).primitive.toList = [26, 0, 0, 0, 0, 72, 132, 164, 0, 68, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0996]
  rfl

theorem primitive_values_0997 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380797) = [28, 0, 0, 0, 0, 88, 204, 220, 0, 124, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0997_semantics :
    (Generated.hostChunk083[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[1]).mask = 380797 := by decide +kernel
  have hv : (Generated.hostChunk083[1]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 220, 0, 124, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0997]
  rfl

theorem primitive_values_0998 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380798) = [28, 0, 0, 0, 0, 86, 186, 214, 0, 102, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0998_semantics :
    (Generated.hostChunk083[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[2]).mask = 380798 := by decide +kernel
  have hv : (Generated.hostChunk083[2]).primitive.toList = [28, 0, 0, 0, 0, 86, 186, 214, 0, 102, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0998]
  rfl

theorem primitive_values_0999 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380799) = [30, 0, 0, 0, 0, 104, 282, 280, 0, 186, 44, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 116] := by
  decide +kernel

theorem primitive_host_0999_semantics :
    (Generated.hostChunk083[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[3]).mask = 380799 := by decide +kernel
  have hv : (Generated.hostChunk083[3]).primitive.toList = [30, 0, 0, 0, 0, 104, 282, 280, 0, 186, 44, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 116] := by decide +kernel
  rw [hm, hv, primitive_values_0999]
  rfl

theorem primitive_values_1000 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380863) = [30, 0, 0, 0, 0, 106, 300, 288, 0, 212, 32, 0, 0, 120, 0, 8, 0, 0, 0, 0, 0, 152] := by
  decide +kernel

theorem primitive_host_1000_semantics :
    (Generated.hostChunk083[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[4]).mask = 380863 := by decide +kernel
  have hv : (Generated.hostChunk083[4]).primitive.toList = [30, 0, 0, 0, 0, 106, 300, 288, 0, 212, 32, 0, 0, 120, 0, 8, 0, 0, 0, 0, 0, 152] := by decide +kernel
  rw [hm, hv, primitive_values_1000]
  rfl

theorem primitive_values_1001 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380926) = [30, 0, 0, 0, 0, 102, 258, 276, 0, 162, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by
  decide +kernel

theorem primitive_host_1001_semantics :
    (Generated.hostChunk083[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[5]).mask = 380926 := by decide +kernel
  have hv : (Generated.hostChunk083[5]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 276, 0, 162, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by decide +kernel
  rw [hm, hv, primitive_values_1001]
  rfl

theorem primitive_values_1002 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 380927) = [32, 0, 0, 0, 0, 122, 378, 356, 0, 282, 44, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 212] := by
  decide +kernel

theorem primitive_host_1002_semantics :
    (Generated.hostChunk083[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[6]).mask = 380927 := by decide +kernel
  have hv : (Generated.hostChunk083[6]).primitive.toList = [32, 0, 0, 0, 0, 122, 378, 356, 0, 282, 44, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 212] := by decide +kernel
  rw [hm, hv, primitive_values_1002]
  rfl

theorem primitive_values_1003 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384501) = [28, 10, 16, 12, 16, 88, 204, 220, 12, 124, 40, 0, 0, 24, 4, 0, 12, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_1003_semantics :
    (Generated.hostChunk083[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[7]).mask = 384501 := by decide +kernel
  have hv : (Generated.hostChunk083[7]).primitive.toList = [28, 10, 16, 12, 16, 88, 204, 220, 12, 124, 40, 0, 0, 24, 4, 0, 12, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_1003]
  rfl

theorem primitive_values_1004 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384503) = [30, 0, 0, 0, 0, 104, 276, 284, 0, 188, 48, 0, 0, 72, 0, 8, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_1004_semantics :
    (Generated.hostChunk083[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[8]).mask = 384503 := by decide +kernel
  have hv : (Generated.hostChunk083[8]).primitive.toList = [30, 0, 0, 0, 0, 104, 276, 284, 0, 188, 48, 0, 0, 72, 0, 8, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_1004]
  rfl

theorem primitive_values_1005 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384511) = [32, 0, 0, 0, 0, 122, 372, 360, 0, 284, 48, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 216] := by
  decide +kernel

theorem primitive_host_1005_semantics :
    (Generated.hostChunk083[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[9]).mask = 384511 := by decide +kernel
  have hv : (Generated.hostChunk083[9]).primitive.toList = [32, 0, 0, 0, 0, 122, 372, 360, 0, 284, 48, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 216] := by decide +kernel
  rw [hm, hv, primitive_values_1005]
  rfl

theorem primitive_values_1006 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384697) = [26, 20, 32, 24, 0, 72, 132, 164, 0, 68, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_1006_semantics :
    (Generated.hostChunk083[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[10]).mask = 384697 := by decide +kernel
  have hv : (Generated.hostChunk083[10]).primitive.toList = [26, 20, 32, 24, 0, 72, 132, 164, 0, 68, 24, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_1006]
  rfl

theorem primitive_values_1007 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384699) = [28, 10, 18, 16, 0, 86, 186, 214, 0, 102, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_1007_semantics :
    (Generated.hostChunk083[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk083[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk083[11]).mask = 384699 := by decide +kernel
  have hv : (Generated.hostChunk083[11]).primitive.toList = [28, 10, 18, 16, 0, 86, 186, 214, 0, 102, 40, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_1007]
  rfl

theorem primitive_chunk_083_semantics :
    ∀ h ∈ Generated.hostChunk083.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk083.toList = [Generated.hostChunk083[0], Generated.hostChunk083[1], Generated.hostChunk083[2], Generated.hostChunk083[3], Generated.hostChunk083[4], Generated.hostChunk083[5], Generated.hostChunk083[6], Generated.hostChunk083[7], Generated.hostChunk083[8], Generated.hostChunk083[9], Generated.hostChunk083[10], Generated.hostChunk083[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0996_semantics
  · exact primitive_host_0997_semantics
  · exact primitive_host_0998_semantics
  · exact primitive_host_0999_semantics
  · exact primitive_host_1000_semantics
  · exact primitive_host_1001_semantics
  · exact primitive_host_1002_semantics
  · exact primitive_host_1003_semantics
  · exact primitive_host_1004_semantics
  · exact primitive_host_1005_semantics
  · exact primitive_host_1006_semantics
  · exact primitive_host_1007_semantics

end InducedPentagons.Paper

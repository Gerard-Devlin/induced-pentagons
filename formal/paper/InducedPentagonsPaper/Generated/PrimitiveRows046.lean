import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData046
import InducedPentagonsPaper.Generated.PrimitiveRows038

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0552 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43900) = [20, 0, 0, 0, 0, 42, 54, 72, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0552_semantics :
    (Generated.hostChunk046[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[0]).mask = 43900 := by decide +kernel
  have hv : (Generated.hostChunk046[0]).primitive.toList = [20, 0, 0, 0, 0, 42, 54, 72, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0552]
  rfl

theorem primitive_values_0553 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43901) = [22, 0, 0, 0, 0, 56, 108, 108, 0, 42, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0553_semantics :
    (Generated.hostChunk046[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[1]).mask = 43901 := by decide +kernel
  have hv : (Generated.hostChunk046[1]).primitive.toList = [22, 0, 0, 0, 0, 56, 108, 108, 0, 42, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0553]
  rfl

theorem primitive_values_0554 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43903) = [24, 0, 0, 0, 0, 72, 186, 152, 0, 94, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0554_semantics :
    (Generated.hostChunk046[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[2]).mask = 43903 := by decide +kernel
  have hv : (Generated.hostChunk046[2]).primitive.toList = [24, 0, 0, 0, 0, 72, 186, 152, 0, 94, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0554]
  rfl

theorem primitive_values_0555 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43998) = [22, 0, 0, 0, 0, 60, 108, 126, 0, 64, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0555_semantics :
    (Generated.hostChunk046[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[3]).mask = 43998 := by decide +kernel
  have hv : (Generated.hostChunk046[3]).primitive.toList = [22, 0, 0, 0, 0, 60, 108, 126, 0, 64, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0555]
  rfl

theorem primitive_values_0556 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43999) = [24, 0, 0, 0, 0, 76, 180, 174, 0, 136, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0556_semantics :
    (Generated.hostChunk046[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[4]).mask = 43999 := by decide +kernel
  have hv : (Generated.hostChunk046[4]).primitive.toList = [24, 0, 0, 0, 0, 76, 180, 174, 0, 136, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0556]
  rfl

theorem primitive_values_0557 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44006) = [20, 0, 0, 0, 0, 46, 78, 78, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0557_semantics :
    (Generated.hostChunk046[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[5]).mask = 44006 := by decide +kernel
  have hv : (Generated.hostChunk046[5]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 78, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0557]
  rfl

theorem primitive_values_0558 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44007) = [22, 0, 0, 0, 0, 60, 132, 118, 0, 74, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0558_semantics :
    (Generated.hostChunk046[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[6]).mask = 44007 := by decide +kernel
  have hv : (Generated.hostChunk046[6]).primitive.toList = [22, 0, 0, 0, 0, 60, 132, 118, 0, 74, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0558]
  rfl

theorem primitive_values_0559 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44008) = [18, 0, 0, 0, 0, 34, 42, 48, 0, 22, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0559_semantics :
    (Generated.hostChunk046[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[7]).mask = 44008 := by decide +kernel
  have hv : (Generated.hostChunk046[7]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 48, 0, 22, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0559]
  rfl

theorem primitive_values_0560 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44009) = [20, 0, 0, 0, 0, 46, 84, 76, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0560_semantics :
    (Generated.hostChunk046[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[8]).mask = 44009 := by decide +kernel
  have hv : (Generated.hostChunk046[8]).primitive.toList = [20, 0, 0, 0, 0, 46, 84, 76, 0, 38, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0560]
  rfl

theorem primitive_values_0561 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44010) = [20, 0, 0, 0, 0, 44, 66, 76, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0561_semantics :
    (Generated.hostChunk046[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[9]).mask = 44010 := by decide +kernel
  have hv : (Generated.hostChunk046[9]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 76, 0, 26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0561]
  rfl

theorem primitive_values_0562 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44011) = [22, 0, 0, 0, 0, 58, 120, 114, 0, 58, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0562_semantics :
    (Generated.hostChunk046[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[10]).mask = 44011 := by decide +kernel
  have hv : (Generated.hostChunk046[10]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 114, 0, 58, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0562]
  rfl

theorem primitive_values_0563 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44012) = [20, 0, 0, 0, 0, 44, 66, 72, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0563_semantics :
    (Generated.hostChunk046[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk046[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk046[11]).mask = 44012 := by decide +kernel
  have hv : (Generated.hostChunk046[11]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 72, 0, 34, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0563]
  rfl

theorem primitive_chunk_046_semantics :
    ∀ h ∈ Generated.hostChunk046.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk046.toList = [Generated.hostChunk046[0], Generated.hostChunk046[1], Generated.hostChunk046[2], Generated.hostChunk046[3], Generated.hostChunk046[4], Generated.hostChunk046[5], Generated.hostChunk046[6], Generated.hostChunk046[7], Generated.hostChunk046[8], Generated.hostChunk046[9], Generated.hostChunk046[10], Generated.hostChunk046[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0552_semantics
  · exact primitive_host_0553_semantics
  · exact primitive_host_0554_semantics
  · exact primitive_host_0555_semantics
  · exact primitive_host_0556_semantics
  · exact primitive_host_0557_semantics
  · exact primitive_host_0558_semantics
  · exact primitive_host_0559_semantics
  · exact primitive_host_0560_semantics
  · exact primitive_host_0561_semantics
  · exact primitive_host_0562_semantics
  · exact primitive_host_0563_semantics

end InducedPentagons.Paper

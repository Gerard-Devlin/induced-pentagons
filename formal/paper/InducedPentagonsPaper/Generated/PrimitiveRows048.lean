import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData048
import InducedPentagonsPaper.Generated.PrimitiveRows040

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0576 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44287) = [24, 0, 0, 0, 0, 72, 192, 150, 0, 96, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 6, 48] := by
  decide +kernel

theorem primitive_host_0576_semantics :
    (Generated.hostChunk048[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[0]).mask = 44287 := by decide +kernel
  have hv : (Generated.hostChunk048[0]).primitive.toList = [24, 0, 0, 0, 0, 72, 192, 150, 0, 96, 24, 0, 0, 24, 0, 0, 0, 0, 0, 0, 6, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0576]
  rfl

theorem primitive_values_0577 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44336) = [14, 0, 0, 0, 0, 14, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0577_semantics :
    (Generated.hostChunk048[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[1]).mask = 44336 := by decide +kernel
  have hv : (Generated.hostChunk048[1]).primitive.toList = [14, 0, 0, 0, 0, 14, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0577]
  rfl

theorem primitive_values_0578 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44337) = [16, 0, 0, 0, 0, 22, 12, 24, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0578_semantics :
    (Generated.hostChunk048[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[2]).mask = 44337 := by decide +kernel
  have hv : (Generated.hostChunk048[2]).primitive.toList = [16, 0, 0, 0, 0, 22, 12, 24, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0578]
  rfl

theorem primitive_values_0579 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44339) = [18, 10, 8, 4, 0, 32, 36, 42, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0579_semantics :
    (Generated.hostChunk048[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[3]).mask = 44339 := by decide +kernel
  have hv : (Generated.hostChunk048[3]).primitive.toList = [18, 10, 8, 4, 0, 32, 36, 42, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0579]
  rfl

theorem primitive_values_0580 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44340) = [16, 10, 4, 0, 4, 22, 12, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0580_semantics :
    (Generated.hostChunk048[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[4]).mask = 44340 := by decide +kernel
  have hv : (Generated.hostChunk048[4]).primitive.toList = [16, 10, 4, 0, 4, 22, 12, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0580]
  rfl

theorem primitive_values_0581 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44341) = [18, 0, 0, 0, 0, 32, 36, 48, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0581_semantics :
    (Generated.hostChunk048[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[5]).mask = 44341 := by decide +kernel
  have hv : (Generated.hostChunk048[5]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 48, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0581]
  rfl

theorem primitive_values_0582 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44342) = [18, 10, 6, 4, 6, 32, 36, 44, 4, 14, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0582_semantics :
    (Generated.hostChunk048[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[6]).mask = 44342 := by decide +kernel
  have hv : (Generated.hostChunk048[6]).primitive.toList = [18, 10, 6, 4, 6, 32, 36, 44, 4, 14, 4, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0582]
  rfl

theorem primitive_values_0583 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44343) = [20, 0, 0, 0, 0, 44, 78, 70, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0583_semantics :
    (Generated.hostChunk048[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[7]).mask = 44343 := by decide +kernel
  have hv : (Generated.hostChunk048[7]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 70, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0583]
  rfl

theorem primitive_values_0584 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44348) = [18, 0, 0, 0, 0, 32, 36, 50, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0584_semantics :
    (Generated.hostChunk048[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[8]).mask = 44348 := by decide +kernel
  have hv : (Generated.hostChunk048[8]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 50, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0584]
  rfl

theorem primitive_values_0585 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44349) = [20, 0, 0, 0, 0, 44, 78, 72, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0585_semantics :
    (Generated.hostChunk048[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[9]).mask = 44349 := by decide +kernel
  have hv : (Generated.hostChunk048[9]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 72, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0585]
  rfl

theorem primitive_values_0586 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44351) = [22, 0, 0, 0, 0, 58, 144, 102, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0586_semantics :
    (Generated.hostChunk048[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[10]).mask = 44351 := by decide +kernel
  have hv : (Generated.hostChunk048[10]).primitive.toList = [22, 0, 0, 0, 0, 58, 144, 102, 0, 56, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0586]
  rfl

theorem primitive_values_0587 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 44403) = [20, 0, 0, 0, 0, 44, 72, 74, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0587_semantics :
    (Generated.hostChunk048[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk048[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk048[11]).mask = 44403 := by decide +kernel
  have hv : (Generated.hostChunk048[11]).primitive.toList = [20, 0, 0, 0, 0, 44, 72, 74, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0587]
  rfl

theorem primitive_chunk_048_semantics :
    ∀ h ∈ Generated.hostChunk048.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk048.toList = [Generated.hostChunk048[0], Generated.hostChunk048[1], Generated.hostChunk048[2], Generated.hostChunk048[3], Generated.hostChunk048[4], Generated.hostChunk048[5], Generated.hostChunk048[6], Generated.hostChunk048[7], Generated.hostChunk048[8], Generated.hostChunk048[9], Generated.hostChunk048[10], Generated.hostChunk048[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0576_semantics
  · exact primitive_host_0577_semantics
  · exact primitive_host_0578_semantics
  · exact primitive_host_0579_semantics
  · exact primitive_host_0580_semantics
  · exact primitive_host_0581_semantics
  · exact primitive_host_0582_semantics
  · exact primitive_host_0583_semantics
  · exact primitive_host_0584_semantics
  · exact primitive_host_0585_semantics
  · exact primitive_host_0586_semantics
  · exact primitive_host_0587_semantics

end InducedPentagons.Paper

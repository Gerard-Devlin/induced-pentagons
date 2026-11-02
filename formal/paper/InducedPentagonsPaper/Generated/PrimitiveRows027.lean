import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData027
import InducedPentagonsPaper.Generated.PrimitiveRows019

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0324 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15261) = [20, 0, 0, 0, 0, 48, 72, 96, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0324_semantics :
    (Generated.hostChunk027[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[0]).mask = 15261 := by decide +kernel
  have hv : (Generated.hostChunk027[0]).primitive.toList = [20, 0, 0, 0, 0, 48, 72, 96, 0, 30, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0324]
  rfl

theorem primitive_values_0325 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15263) = [22, 0, 0, 0, 0, 62, 126, 132, 0, 72, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0325_semantics :
    (Generated.hostChunk027[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[1]).mask = 15263 := by decide +kernel
  have hv : (Generated.hostChunk027[1]).primitive.toList = [22, 0, 0, 0, 0, 62, 126, 132, 0, 72, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0325]
  rfl

theorem primitive_values_0326 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15276) = [18, 0, 0, 0, 0, 32, 30, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0326_semantics :
    (Generated.hostChunk027[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[2]).mask = 15276 := by decide +kernel
  have hv : (Generated.hostChunk027[2]).primitive.toList = [18, 0, 0, 0, 0, 32, 30, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0326]
  rfl

theorem primitive_values_0327 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15277) = [20, 0, 0, 0, 0, 44, 66, 80, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0327_semantics :
    (Generated.hostChunk027[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[3]).mask = 15277 := by decide +kernel
  have hv : (Generated.hostChunk027[3]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 80, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0327]
  rfl

theorem primitive_values_0328 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15279) = [22, 0, 0, 0, 0, 58, 120, 116, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0328_semantics :
    (Generated.hostChunk027[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[4]).mask = 15279 := by decide +kernel
  have hv : (Generated.hostChunk027[4]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 116, 0, 48, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0328]
  rfl

theorem primitive_values_0329 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15292) = [20, 0, 0, 0, 0, 42, 54, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0329_semantics :
    (Generated.hostChunk027[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[5]).mask = 15292 := by decide +kernel
  have hv : (Generated.hostChunk027[5]).primitive.toList = [20, 0, 0, 0, 0, 42, 54, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0329]
  rfl

theorem primitive_values_0330 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15293) = [22, 0, 0, 0, 0, 56, 108, 114, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0330_semantics :
    (Generated.hostChunk027[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[6]).mask = 15293 := by decide +kernel
  have hv : (Generated.hostChunk027[6]).primitive.toList = [22, 0, 0, 0, 0, 56, 108, 114, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0330]
  rfl

theorem primitive_values_0331 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15295) = [24, 0, 0, 0, 0, 72, 186, 156, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0331_semantics :
    (Generated.hostChunk027[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[7]).mask = 15295 := by decide +kernel
  have hv : (Generated.hostChunk027[7]).primitive.toList = [24, 0, 0, 0, 0, 72, 186, 156, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0331]
  rfl

theorem primitive_values_0332 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15327) = [24, 0, 0, 0, 0, 78, 198, 180, 0, 144, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0332_semantics :
    (Generated.hostChunk027[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[8]).mask = 15327 := by decide +kernel
  have hv : (Generated.hostChunk027[8]).primitive.toList = [24, 0, 0, 0, 0, 78, 198, 180, 0, 144, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0332]
  rfl

theorem primitive_values_0333 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15340) = [20, 0, 0, 0, 0, 44, 66, 76, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0333_semantics :
    (Generated.hostChunk027[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[9]).mask = 15340 := by decide +kernel
  have hv : (Generated.hostChunk027[9]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 76, 0, 28, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0333]
  rfl

theorem primitive_values_0334 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15341) = [22, 0, 0, 0, 0, 58, 120, 112, 0, 58, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0334_semantics :
    (Generated.hostChunk027[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[10]).mask = 15341 := by decide +kernel
  have hv : (Generated.hostChunk027[10]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 112, 0, 58, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0334]
  rfl

theorem primitive_values_0335 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15343) = [24, 0, 0, 0, 0, 74, 192, 160, 0, 114, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0335_semantics :
    (Generated.hostChunk027[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk027[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk027[11]).mask = 15343 := by decide +kernel
  have hv : (Generated.hostChunk027[11]).primitive.toList = [24, 0, 0, 0, 0, 74, 192, 160, 0, 114, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0335]
  rfl

theorem primitive_chunk_027_semantics :
    ∀ h ∈ Generated.hostChunk027.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk027.toList = [Generated.hostChunk027[0], Generated.hostChunk027[1], Generated.hostChunk027[2], Generated.hostChunk027[3], Generated.hostChunk027[4], Generated.hostChunk027[5], Generated.hostChunk027[6], Generated.hostChunk027[7], Generated.hostChunk027[8], Generated.hostChunk027[9], Generated.hostChunk027[10], Generated.hostChunk027[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0324_semantics
  · exact primitive_host_0325_semantics
  · exact primitive_host_0326_semantics
  · exact primitive_host_0327_semantics
  · exact primitive_host_0328_semantics
  · exact primitive_host_0329_semantics
  · exact primitive_host_0330_semantics
  · exact primitive_host_0331_semantics
  · exact primitive_host_0332_semantics
  · exact primitive_host_0333_semantics
  · exact primitive_host_0334_semantics
  · exact primitive_host_0335_semantics

end InducedPentagons.Paper

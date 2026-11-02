import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData042
import InducedPentagonsPaper.Generated.PrimitiveRows034

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0504 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42223) = [20, 0, 0, 0, 0, 48, 96, 82, 0, 42, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem primitive_host_0504_semantics :
    (Generated.hostChunk042[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[0]).mask = 42223 := by decide +kernel
  have hv : (Generated.hostChunk042[0]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 82, 0, 42, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by decide +kernel
  rw [hm, hv, primitive_values_0504]
  rfl

theorem primitive_values_0505 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42232) = [16, 20, 8, 0, 8, 22, 12, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0505_semantics :
    (Generated.hostChunk042[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[1]).mask = 42232 := by decide +kernel
  have hv : (Generated.hostChunk042[1]).primitive.toList = [16, 20, 8, 0, 8, 22, 12, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0505]
  rfl

theorem primitive_values_0506 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42233) = [18, 0, 0, 0, 0, 34, 48, 52, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0506_semantics :
    (Generated.hostChunk042[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[2]).mask = 42233 := by decide +kernel
  have hv : (Generated.hostChunk042[2]).primitive.toList = [18, 0, 0, 0, 0, 34, 48, 52, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0506]
  rfl

theorem primitive_values_0507 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42234) = [18, 20, 14, 8, 6, 32, 36, 46, 4, 6, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0507_semantics :
    (Generated.hostChunk042[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[3]).mask = 42234 := by decide +kernel
  have hv : (Generated.hostChunk042[3]).primitive.toList = [18, 20, 14, 8, 6, 32, 36, 46, 4, 6, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0507]
  rfl

theorem primitive_values_0508 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42235) = [20, 0, 0, 0, 0, 46, 90, 76, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 8] := by
  decide +kernel

theorem primitive_host_0508_semantics :
    (Generated.hostChunk042[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[4]).mask = 42235 := by decide +kernel
  have hv : (Generated.hostChunk042[4]).primitive.toList = [20, 0, 0, 0, 0, 46, 90, 76, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0508]
  rfl

theorem primitive_values_0509 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42238) = [20, 0, 0, 0, 0, 44, 78, 72, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0509_semantics :
    (Generated.hostChunk042[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[5]).mask = 42238 := by decide +kernel
  have hv : (Generated.hostChunk042[5]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 72, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0509]
  rfl

theorem primitive_values_0510 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42239) = [22, 0, 0, 0, 0, 60, 156, 108, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0510_semantics :
    (Generated.hostChunk042[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[6]).mask = 42239 := by decide +kernel
  have hv : (Generated.hostChunk042[6]).primitive.toList = [22, 0, 0, 0, 0, 60, 156, 108, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0510]
  rfl

theorem primitive_values_0511 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42412) = [16, 0, 0, 0, 0, 26, 24, 36, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0511_semantics :
    (Generated.hostChunk042[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[7]).mask = 42412 := by decide +kernel
  have hv : (Generated.hostChunk042[7]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 36, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0511]
  rfl

theorem primitive_values_0512 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42413) = [18, 0, 0, 0, 0, 38, 60, 56, 0, 44, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0512_semantics :
    (Generated.hostChunk042[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[8]).mask = 42413 := by decide +kernel
  have hv : (Generated.hostChunk042[8]).primitive.toList = [18, 0, 0, 0, 0, 38, 60, 56, 0, 44, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0512]
  rfl

theorem primitive_values_0513 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42414) = [18, 0, 0, 0, 0, 34, 42, 52, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0513_semantics :
    (Generated.hostChunk042[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[9]).mask = 42414 := by decide +kernel
  have hv : (Generated.hostChunk042[9]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 52, 0, 14, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0513]
  rfl

theorem primitive_values_0514 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42415) = [20, 0, 0, 0, 0, 48, 96, 80, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0514_semantics :
    (Generated.hostChunk042[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[10]).mask = 42415 := by decide +kernel
  have hv : (Generated.hostChunk042[10]).primitive.toList = [20, 0, 0, 0, 0, 48, 96, 80, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0514]
  rfl

theorem primitive_values_0515 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42418) = [16, 0, 0, 0, 0, 22, 12, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0515_semantics :
    (Generated.hostChunk042[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk042[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk042[11]).mask = 42418 := by decide +kernel
  have hv : (Generated.hostChunk042[11]).primitive.toList = [16, 0, 0, 0, 0, 22, 12, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0515]
  rfl

theorem primitive_chunk_042_semantics :
    ∀ h ∈ Generated.hostChunk042.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk042.toList = [Generated.hostChunk042[0], Generated.hostChunk042[1], Generated.hostChunk042[2], Generated.hostChunk042[3], Generated.hostChunk042[4], Generated.hostChunk042[5], Generated.hostChunk042[6], Generated.hostChunk042[7], Generated.hostChunk042[8], Generated.hostChunk042[9], Generated.hostChunk042[10], Generated.hostChunk042[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0504_semantics
  · exact primitive_host_0505_semantics
  · exact primitive_host_0506_semantics
  · exact primitive_host_0507_semantics
  · exact primitive_host_0508_semantics
  · exact primitive_host_0509_semantics
  · exact primitive_host_0510_semantics
  · exact primitive_host_0511_semantics
  · exact primitive_host_0512_semantics
  · exact primitive_host_0513_semantics
  · exact primitive_host_0514_semantics
  · exact primitive_host_0515_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData085
import InducedPentagonsPaper.Generated.PrimitiveRows077

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_1020 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 393151) = [34, 0, 0, 0, 0, 136, 426, 432, 0, 338, 52, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 268] := by
  decide +kernel

theorem primitive_host_1020_semantics :
    (Generated.hostChunk085[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[0]).mask = 393151 := by decide +kernel
  have hv : (Generated.hostChunk085[0]).primitive.toList = [34, 0, 0, 0, 0, 136, 426, 432, 0, 338, 52, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 268] := by decide +kernel
  rw [hm, hv, primitive_values_1020]
  rfl

theorem primitive_values_1021 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 393215) = [36, 0, 0, 0, 0, 156, 546, 528, 0, 474, 36, 0, 0, 384, 0, 0, 0, 0, 0, 0, 0, 420] := by
  decide +kernel

theorem primitive_host_1021_semantics :
    (Generated.hostChunk085[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[1]).mask = 393215 := by decide +kernel
  have hv : (Generated.hostChunk085[1]).primitive.toList = [36, 0, 0, 0, 0, 156, 546, 528, 0, 474, 36, 0, 0, 384, 0, 0, 0, 0, 0, 0, 0, 420] := by decide +kernel
  rw [hm, hv, primitive_values_1021]
  rfl

theorem primitive_values_1022 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 425917) = [30, 0, 0, 0, 0, 100, 240, 272, 0, 144, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by
  decide +kernel

theorem primitive_host_1022_semantics :
    (Generated.hostChunk085[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[2]).mask = 425917 := by decide +kernel
  have hv : (Generated.hostChunk085[2]).primitive.toList = [30, 0, 0, 0, 0, 100, 240, 272, 0, 144, 32, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 80] := by decide +kernel
  rw [hm, hv, primitive_values_1022]
  rfl

theorem primitive_values_1023 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 425919) = [32, 0, 0, 0, 0, 118, 336, 344, 0, 232, 56, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 152] := by
  decide +kernel

theorem primitive_host_1023_semantics :
    (Generated.hostChunk085[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[3]).mask = 425919 := by decide +kernel
  have hv : (Generated.hostChunk085[3]).primitive.toList = [32, 0, 0, 0, 0, 118, 336, 344, 0, 232, 56, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 152] := by decide +kernel
  rw [hm, hv, primitive_values_1023]
  rfl

theorem primitive_values_1024 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 425983) = [34, 0, 0, 0, 0, 138, 456, 432, 0, 360, 48, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 288] := by
  decide +kernel

theorem primitive_host_1024_semantics :
    (Generated.hostChunk085[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[4]).mask = 425983 := by decide +kernel
  have hv : (Generated.hostChunk085[4]).primitive.toList = [34, 0, 0, 0, 0, 138, 456, 432, 0, 360, 48, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 288] := by decide +kernel
  rw [hm, hv, primitive_values_1024]
  rfl

theorem primitive_values_1025 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 452606) = [30, 10, 20, 20, 0, 100, 240, 270, 0, 140, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_1025_semantics :
    (Generated.hostChunk085[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[5]).mask = 452606 := by decide +kernel
  have hv : (Generated.hostChunk085[5]).primitive.toList = [30, 10, 20, 20, 0, 100, 240, 270, 0, 140, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_1025]
  rfl

theorem primitive_values_1026 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 452607) = [32, 10, 20, 20, 20, 120, 360, 350, 20, 260, 60, 0, 0, 120, 20, 0, 20, 0, 0, 0, 0, 180] := by
  decide +kernel

theorem primitive_host_1026_semantics :
    (Generated.hostChunk085[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[6]).mask = 452607 := by decide +kernel
  have hv : (Generated.hostChunk085[6]).primitive.toList = [32, 10, 20, 20, 20, 120, 360, 350, 20, 260, 60, 0, 0, 120, 20, 0, 20, 0, 0, 0, 0, 180] := by decide +kernel
  rw [hm, hv, primitive_values_1026]
  rfl

theorem primitive_values_1027 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 454463) = [30, 0, 0, 0, 0, 102, 264, 276, 0, 168, 48, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 96] := by
  decide +kernel

theorem primitive_host_1027_semantics :
    (Generated.hostChunk085[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[7]).mask = 454463 := by decide +kernel
  have hv : (Generated.hostChunk085[7]).primitive.toList = [30, 0, 0, 0, 0, 102, 264, 276, 0, 168, 48, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 96] := by decide +kernel
  rw [hm, hv, primitive_values_1027]
  rfl

theorem primitive_values_1028 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 454524) = [28, 0, 0, 0, 0, 84, 168, 210, 0, 84, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_1028_semantics :
    (Generated.hostChunk085[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[8]).mask = 454524 := by decide +kernel
  have hv : (Generated.hostChunk085[8]).primitive.toList = [28, 0, 0, 0, 0, 84, 168, 210, 0, 84, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_1028]
  rfl

theorem primitive_values_1029 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 454525) = [30, 0, 0, 0, 0, 100, 240, 272, 0, 144, 48, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_1029_semantics :
    (Generated.hostChunk085[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[9]).mask = 454525 := by decide +kernel
  have hv : (Generated.hostChunk085[9]).primitive.toList = [30, 0, 0, 0, 0, 100, 240, 272, 0, 144, 48, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_1029]
  rfl

theorem primitive_values_1030 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 454527) = [32, 0, 0, 0, 0, 118, 336, 346, 0, 236, 60, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 156] := by
  decide +kernel

theorem primitive_host_1030_semantics :
    (Generated.hostChunk085[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[10]).mask = 454527 := by decide +kernel
  have hv : (Generated.hostChunk085[10]).primitive.toList = [32, 0, 0, 0, 0, 118, 336, 346, 0, 236, 60, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 156] := by decide +kernel
  rw [hm, hv, primitive_values_1030]
  rfl

theorem primitive_values_1031 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 454654) = [32, 0, 0, 0, 0, 116, 312, 340, 0, 208, 72, 0, 4, 48, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_1031_semantics :
    (Generated.hostChunk085[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk085[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk085[11]).mask = 454654 := by decide +kernel
  have hv : (Generated.hostChunk085[11]).primitive.toList = [32, 0, 0, 0, 0, 116, 312, 340, 0, 208, 72, 0, 4, 48, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_1031]
  rfl

theorem primitive_chunk_085_semantics :
    ∀ h ∈ Generated.hostChunk085.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk085.toList = [Generated.hostChunk085[0], Generated.hostChunk085[1], Generated.hostChunk085[2], Generated.hostChunk085[3], Generated.hostChunk085[4], Generated.hostChunk085[5], Generated.hostChunk085[6], Generated.hostChunk085[7], Generated.hostChunk085[8], Generated.hostChunk085[9], Generated.hostChunk085[10], Generated.hostChunk085[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_1020_semantics
  · exact primitive_host_1021_semantics
  · exact primitive_host_1022_semantics
  · exact primitive_host_1023_semantics
  · exact primitive_host_1024_semantics
  · exact primitive_host_1025_semantics
  · exact primitive_host_1026_semantics
  · exact primitive_host_1027_semantics
  · exact primitive_host_1028_semantics
  · exact primitive_host_1029_semantics
  · exact primitive_host_1030_semantics
  · exact primitive_host_1031_semantics

end InducedPentagons.Paper

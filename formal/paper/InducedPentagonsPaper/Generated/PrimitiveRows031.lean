import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData031
import InducedPentagonsPaper.Generated.PrimitiveRows023

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0372 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39447) = [16, 0, 0, 0, 0, 30, 36, 36, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0372_semantics :
    (Generated.hostChunk031[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[0]).mask = 39447 := by decide +kernel
  have hv : (Generated.hostChunk031[0]).primitive.toList = [16, 0, 0, 0, 0, 30, 36, 36, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0372]
  rfl

theorem primitive_values_0373 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39455) = [18, 0, 0, 0, 0, 42, 78, 60, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0373_semantics :
    (Generated.hostChunk031[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[1]).mask = 39455 := by decide +kernel
  have hv : (Generated.hostChunk031[1]).primitive.toList = [18, 0, 0, 0, 0, 42, 78, 60, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0373]
  rfl

theorem primitive_values_0374 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39456) = [10, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0374_semantics :
    (Generated.hostChunk031[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[2]).mask = 39456 := by decide +kernel
  have hv : (Generated.hostChunk031[2]).primitive.toList = [10, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0374]
  rfl

theorem primitive_values_0375 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39457) = [12, 0, 0, 0, 0, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0375_semantics :
    (Generated.hostChunk031[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[3]).mask = 39457 := by decide +kernel
  have hv : (Generated.hostChunk031[3]).primitive.toList = [12, 0, 0, 0, 0, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0375]
  rfl

theorem primitive_values_0376 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39458) = [12, 0, 0, 0, 0, 12, 6, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0376_semantics :
    (Generated.hostChunk031[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[4]).mask = 39458 := by decide +kernel
  have hv : (Generated.hostChunk031[4]).primitive.toList = [12, 0, 0, 0, 0, 12, 6, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0376]
  rfl

theorem primitive_values_0377 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39459) = [14, 0, 0, 0, 0, 18, 12, 16, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0377_semantics :
    (Generated.hostChunk031[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[5]).mask = 39459 := by decide +kernel
  have hv : (Generated.hostChunk031[5]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 16, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0377]
  rfl

theorem primitive_values_0378 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39462) = [14, 0, 0, 0, 0, 20, 18, 20, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0378_semantics :
    (Generated.hostChunk031[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[6]).mask = 39462 := by decide +kernel
  have hv : (Generated.hostChunk031[6]).primitive.toList = [14, 0, 0, 0, 0, 20, 18, 20, 0, 10, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0378]
  rfl

theorem primitive_values_0379 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39463) = [16, 0, 0, 0, 0, 28, 36, 34, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0379_semantics :
    (Generated.hostChunk031[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[7]).mask = 39463 := by decide +kernel
  have hv : (Generated.hostChunk031[7]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 34, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0379]
  rfl

theorem primitive_values_0380 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39470) = [16, 0, 0, 0, 0, 30, 42, 36, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0380_semantics :
    (Generated.hostChunk031[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[8]).mask = 39470 := by decide +kernel
  have hv : (Generated.hostChunk031[8]).primitive.toList = [16, 0, 0, 0, 0, 30, 42, 36, 0, 30, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0380]
  rfl

theorem primitive_values_0381 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39471) = [18, 0, 0, 0, 0, 40, 78, 56, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0381_semantics :
    (Generated.hostChunk031[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[9]).mask = 39471 := by decide +kernel
  have hv : (Generated.hostChunk031[9]).primitive.toList = [18, 0, 0, 0, 0, 40, 78, 56, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0381]
  rfl

theorem primitive_values_0382 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39473) = [14, 0, 0, 0, 0, 16, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0382_semantics :
    (Generated.hostChunk031[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[10]).mask = 39473 := by decide +kernel
  have hv : (Generated.hostChunk031[10]).primitive.toList = [14, 0, 0, 0, 0, 16, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0382]
  rfl

theorem primitive_values_0383 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39475) = [16, 0, 0, 0, 0, 26, 30, 24, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0383_semantics :
    (Generated.hostChunk031[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk031[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk031[11]).mask = 39475 := by decide +kernel
  have hv : (Generated.hostChunk031[11]).primitive.toList = [16, 0, 0, 0, 0, 26, 30, 24, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0383]
  rfl

theorem primitive_chunk_031_semantics :
    ∀ h ∈ Generated.hostChunk031.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk031.toList = [Generated.hostChunk031[0], Generated.hostChunk031[1], Generated.hostChunk031[2], Generated.hostChunk031[3], Generated.hostChunk031[4], Generated.hostChunk031[5], Generated.hostChunk031[6], Generated.hostChunk031[7], Generated.hostChunk031[8], Generated.hostChunk031[9], Generated.hostChunk031[10], Generated.hostChunk031[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0372_semantics
  · exact primitive_host_0373_semantics
  · exact primitive_host_0374_semantics
  · exact primitive_host_0375_semantics
  · exact primitive_host_0376_semantics
  · exact primitive_host_0377_semantics
  · exact primitive_host_0378_semantics
  · exact primitive_host_0379_semantics
  · exact primitive_host_0380_semantics
  · exact primitive_host_0381_semantics
  · exact primitive_host_0382_semantics
  · exact primitive_host_0383_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData043
import InducedPentagonsPaper.Generated.PrimitiveRows035

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0516 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42419) = [18, 0, 0, 0, 0, 34, 48, 40, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0516_semantics :
    (Generated.hostChunk043[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[0]).mask = 42419 := by decide +kernel
  have hv : (Generated.hostChunk043[0]).primitive.toList = [18, 0, 0, 0, 0, 34, 48, 40, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0516]
  rfl

theorem primitive_values_0517 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42422) = [18, 0, 0, 0, 0, 32, 36, 40, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0517_semantics :
    (Generated.hostChunk043[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[1]).mask = 42422 := by decide +kernel
  have hv : (Generated.hostChunk043[1]).primitive.toList = [18, 0, 0, 0, 0, 32, 36, 40, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0517]
  rfl

theorem primitive_values_0518 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42423) = [20, 0, 0, 0, 0, 46, 90, 70, 0, 34, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0518_semantics :
    (Generated.hostChunk043[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[2]).mask = 42423 := by decide +kernel
  have hv : (Generated.hostChunk043[2]).primitive.toList = [20, 0, 0, 0, 0, 46, 90, 70, 0, 34, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0518]
  rfl

theorem primitive_values_0519 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42430) = [20, 0, 0, 0, 0, 44, 78, 68, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0519_semantics :
    (Generated.hostChunk043[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[3]).mask = 42430 := by decide +kernel
  have hv : (Generated.hostChunk043[3]).primitive.toList = [20, 0, 0, 0, 0, 44, 78, 68, 0, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0519]
  rfl

theorem primitive_values_0520 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42431) = [22, 0, 0, 0, 0, 60, 156, 104, 0, 68, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0520_semantics :
    (Generated.hostChunk043[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[4]).mask = 42431 := by decide +kernel
  have hv : (Generated.hostChunk043[4]).primitive.toList = [22, 0, 0, 0, 0, 60, 156, 104, 0, 68, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0520]
  rfl

theorem primitive_values_0521 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42478) = [20, 0, 0, 0, 0, 44, 66, 80, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0521_semantics :
    (Generated.hostChunk043[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[5]).mask = 42478 := by decide +kernel
  have hv : (Generated.hostChunk043[5]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 80, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0521]
  rfl

theorem primitive_values_0522 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42479) = [22, 0, 0, 0, 0, 60, 138, 116, 0, 74, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0522_semantics :
    (Generated.hostChunk043[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[6]).mask = 42479 := by decide +kernel
  have hv : (Generated.hostChunk043[6]).primitive.toList = [22, 0, 0, 0, 0, 60, 138, 116, 0, 74, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0522]
  rfl

theorem primitive_values_0523 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42486) = [20, 0, 0, 0, 0, 42, 60, 68, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0523_semantics :
    (Generated.hostChunk043[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[7]).mask = 42486 := by decide +kernel
  have hv : (Generated.hostChunk043[7]).primitive.toList = [20, 0, 0, 0, 0, 42, 60, 68, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0523]
  rfl

theorem primitive_values_0524 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42487) = [22, 0, 0, 0, 0, 58, 132, 106, 0, 56, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0524_semantics :
    (Generated.hostChunk043[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[8]).mask = 42487 := by decide +kernel
  have hv : (Generated.hostChunk043[8]).primitive.toList = [22, 0, 0, 0, 0, 58, 132, 106, 0, 56, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0524]
  rfl

theorem primitive_values_0525 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42492) = [20, 30, 28, 24, 8, 42, 60, 70, 8, 16, 4, 0, 0, 0, 0, 0, 8, 8, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0525_semantics :
    (Generated.hostChunk043[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[9]).mask = 42492 := by decide +kernel
  have hv : (Generated.hostChunk043[9]).primitive.toList = [20, 30, 28, 24, 8, 42, 60, 70, 8, 16, 4, 0, 0, 0, 0, 0, 8, 8, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0525]
  rfl

theorem primitive_values_0526 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42493) = [22, 0, 0, 0, 0, 58, 132, 108, 0, 60, 8, 0, 8, 24, 0, 4, 0, 0, 4, 4, 0, 32] := by
  decide +kernel

theorem primitive_host_0526_semantics :
    (Generated.hostChunk043[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[10]).mask = 42493 := by decide +kernel
  have hv : (Generated.hostChunk043[10]).primitive.toList = [22, 0, 0, 0, 0, 58, 132, 108, 0, 60, 8, 0, 8, 24, 0, 4, 0, 0, 4, 4, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0526]
  rfl

theorem primitive_values_0527 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 42494) = [22, 0, 0, 0, 0, 54, 102, 100, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0527_semantics :
    (Generated.hostChunk043[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk043[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk043[11]).mask = 42494 := by decide +kernel
  have hv : (Generated.hostChunk043[11]).primitive.toList = [22, 0, 0, 0, 0, 54, 102, 100, 0, 26, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0527]
  rfl

theorem primitive_chunk_043_semantics :
    ∀ h ∈ Generated.hostChunk043.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk043.toList = [Generated.hostChunk043[0], Generated.hostChunk043[1], Generated.hostChunk043[2], Generated.hostChunk043[3], Generated.hostChunk043[4], Generated.hostChunk043[5], Generated.hostChunk043[6], Generated.hostChunk043[7], Generated.hostChunk043[8], Generated.hostChunk043[9], Generated.hostChunk043[10], Generated.hostChunk043[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0516_semantics
  · exact primitive_host_0517_semantics
  · exact primitive_host_0518_semantics
  · exact primitive_host_0519_semantics
  · exact primitive_host_0520_semantics
  · exact primitive_host_0521_semantics
  · exact primitive_host_0522_semantics
  · exact primitive_host_0523_semantics
  · exact primitive_host_0524_semantics
  · exact primitive_host_0525_semantics
  · exact primitive_host_0526_semantics
  · exact primitive_host_0527_semantics

end InducedPentagons.Paper

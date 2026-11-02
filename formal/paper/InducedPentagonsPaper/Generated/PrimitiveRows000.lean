import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0000 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 0) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0000_semantics :
    (Generated.hostChunk000[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[0]).mask = 0 := by decide +kernel
  have hv : (Generated.hostChunk000[0]).primitive.toList = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0000]
  rfl

theorem primitive_values_0001 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1) = [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0001_semantics :
    (Generated.hostChunk000[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[1]).mask = 1 := by decide +kernel
  have hv : (Generated.hostChunk000[1]).primitive.toList = [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0001]
  rfl

theorem primitive_values_0002 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 3) = [4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0002_semantics :
    (Generated.hostChunk000[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[2]).mask = 3 := by decide +kernel
  have hv : (Generated.hostChunk000[2]).primitive.toList = [4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0002]
  rfl

theorem primitive_values_0003 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 7) = [6, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0003_semantics :
    (Generated.hostChunk000[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[3]).mask = 7 := by decide +kernel
  have hv : (Generated.hostChunk000[3]).primitive.toList = [6, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0003]
  rfl

theorem primitive_values_0004 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 15) = [8, 0, 0, 0, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0004_semantics :
    (Generated.hostChunk000[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[4]).mask = 15 := by decide +kernel
  have hv : (Generated.hostChunk000[4]).primitive.toList = [8, 0, 0, 0, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0004]
  rfl

theorem primitive_values_0005 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 31) = [10, 0, 0, 0, 0, 20, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0005_semantics :
    (Generated.hostChunk000[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[5]).mask = 31 := by decide +kernel
  have hv : (Generated.hostChunk000[5]).primitive.toList = [10, 0, 0, 0, 0, 20, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0005]
  rfl

theorem primitive_values_0006 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 63) = [12, 0, 0, 0, 0, 30, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0006_semantics :
    (Generated.hostChunk000[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[6]).mask = 63 := by decide +kernel
  have hv : (Generated.hostChunk000[6]).primitive.toList = [12, 0, 0, 0, 0, 30, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0006]
  rfl

theorem primitive_values_0007 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 67) = [6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0007_semantics :
    (Generated.hostChunk000[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[7]).mask = 67 := by decide +kernel
  have hv : (Generated.hostChunk000[7]).primitive.toList = [6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0007]
  rfl

theorem primitive_values_0008 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 68) = [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0008_semantics :
    (Generated.hostChunk000[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[8]).mask = 68 := by decide +kernel
  have hv : (Generated.hostChunk000[8]).primitive.toList = [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0008]
  rfl

theorem primitive_values_0009 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 69) = [6, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0009_semantics :
    (Generated.hostChunk000[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[9]).mask = 69 := by decide +kernel
  have hv : (Generated.hostChunk000[9]).primitive.toList = [6, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0009]
  rfl

theorem primitive_values_0010 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 71) = [8, 0, 0, 0, 0, 10, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0010_semantics :
    (Generated.hostChunk000[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[10]).mask = 71 := by decide +kernel
  have hv : (Generated.hostChunk000[10]).primitive.toList = [8, 0, 0, 0, 0, 10, 6, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0010]
  rfl

theorem primitive_values_0011 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 76) = [6, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0011_semantics :
    (Generated.hostChunk000[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[11]).mask = 76 := by decide +kernel
  have hv : (Generated.hostChunk000[11]).primitive.toList = [6, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0011]
  rfl

theorem primitive_chunk_000_semantics :
    ∀ h ∈ Generated.hostChunk000.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk000.toList = [Generated.hostChunk000[0], Generated.hostChunk000[1], Generated.hostChunk000[2], Generated.hostChunk000[3], Generated.hostChunk000[4], Generated.hostChunk000[5], Generated.hostChunk000[6], Generated.hostChunk000[7], Generated.hostChunk000[8], Generated.hostChunk000[9], Generated.hostChunk000[10], Generated.hostChunk000[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0000_semantics
  · exact primitive_host_0001_semantics
  · exact primitive_host_0002_semantics
  · exact primitive_host_0003_semantics
  · exact primitive_host_0004_semantics
  · exact primitive_host_0005_semantics
  · exact primitive_host_0006_semantics
  · exact primitive_host_0007_semantics
  · exact primitive_host_0008_semantics
  · exact primitive_host_0009_semantics
  · exact primitive_host_0010_semantics
  · exact primitive_host_0011_semantics

end InducedPentagons.Paper

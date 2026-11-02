import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData001

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0012 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 77) = [8, 0, 0, 0, 0, 8, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0012_semantics :
    (Generated.hostChunk001[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[0]).mask = 77 := by decide +kernel
  have hv : (Generated.hostChunk001[0]).primitive.toList = [8, 0, 0, 0, 0, 8, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0012]
  rfl

theorem primitive_values_0013 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 79) = [10, 0, 0, 0, 0, 16, 24, 8, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0013_semantics :
    (Generated.hostChunk001[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[1]).mask = 79 := by decide +kernel
  have hv : (Generated.hostChunk001[1]).primitive.toList = [10, 0, 0, 0, 0, 16, 24, 8, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0013]
  rfl

theorem primitive_values_0014 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 92) = [8, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0014_semantics :
    (Generated.hostChunk001[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[2]).mask = 92 := by decide +kernel
  have hv : (Generated.hostChunk001[2]).primitive.toList = [8, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0014]
  rfl

theorem primitive_values_0015 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 93) = [10, 0, 0, 0, 0, 14, 24, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0015_semantics :
    (Generated.hostChunk001[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[3]).mask = 93 := by decide +kernel
  have hv : (Generated.hostChunk001[3]).primitive.toList = [10, 0, 0, 0, 0, 14, 24, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0015]
  rfl

theorem primitive_values_0016 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 95) = [12, 0, 0, 0, 0, 24, 60, 12, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0016_semantics :
    (Generated.hostChunk001[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[4]).mask = 95 := by decide +kernel
  have hv : (Generated.hostChunk001[4]).primitive.toList = [12, 0, 0, 0, 0, 24, 60, 12, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0016]
  rfl

theorem primitive_values_0017 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 124) = [10, 0, 0, 0, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0017_semantics :
    (Generated.hostChunk001[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[5]).mask = 124 := by decide +kernel
  have hv : (Generated.hostChunk001[5]).primitive.toList = [10, 0, 0, 0, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0017]
  rfl

theorem primitive_values_0018 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 125) = [12, 0, 0, 0, 0, 22, 60, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0018_semantics :
    (Generated.hostChunk001[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[6]).mask = 125 := by decide +kernel
  have hv : (Generated.hostChunk001[6]).primitive.toList = [12, 0, 0, 0, 0, 22, 60, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0018]
  rfl

theorem primitive_values_0019 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 127) = [14, 0, 0, 0, 0, 34, 120, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0019_semantics :
    (Generated.hostChunk001[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[7]).mask = 127 := by decide +kernel
  have hv : (Generated.hostChunk001[7]).primitive.toList = [14, 0, 0, 0, 0, 34, 120, 16, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0019]
  rfl

theorem primitive_values_0020 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 198) = [8, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0020_semantics :
    (Generated.hostChunk001[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[8]).mask = 198 := by decide +kernel
  have hv : (Generated.hostChunk001[8]).primitive.toList = [8, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0020]
  rfl

theorem primitive_values_0021 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 199) = [10, 0, 0, 0, 0, 16, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0021_semantics :
    (Generated.hostChunk001[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[9]).mask = 199 := by decide +kernel
  have hv : (Generated.hostChunk001[9]).primitive.toList = [10, 0, 0, 0, 0, 16, 12, 12, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0021]
  rfl

theorem primitive_values_0022 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 202) = [8, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0022_semantics :
    (Generated.hostChunk001[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[10]).mask = 202 := by decide +kernel
  have hv : (Generated.hostChunk001[10]).primitive.toList = [8, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0022]
  rfl

theorem primitive_values_0023 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 203) = [10, 0, 0, 0, 0, 14, 12, 10, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0023_semantics :
    (Generated.hostChunk001[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk001[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk001[11]).mask = 203 := by decide +kernel
  have hv : (Generated.hostChunk001[11]).primitive.toList = [10, 0, 0, 0, 0, 14, 12, 10, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0023]
  rfl

theorem primitive_chunk_001_semantics :
    ∀ h ∈ Generated.hostChunk001.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk001.toList = [Generated.hostChunk001[0], Generated.hostChunk001[1], Generated.hostChunk001[2], Generated.hostChunk001[3], Generated.hostChunk001[4], Generated.hostChunk001[5], Generated.hostChunk001[6], Generated.hostChunk001[7], Generated.hostChunk001[8], Generated.hostChunk001[9], Generated.hostChunk001[10], Generated.hostChunk001[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0012_semantics
  · exact primitive_host_0013_semantics
  · exact primitive_host_0014_semantics
  · exact primitive_host_0015_semantics
  · exact primitive_host_0016_semantics
  · exact primitive_host_0017_semantics
  · exact primitive_host_0018_semantics
  · exact primitive_host_0019_semantics
  · exact primitive_host_0020_semantics
  · exact primitive_host_0021_semantics
  · exact primitive_host_0022_semantics
  · exact primitive_host_0023_semantics

end InducedPentagons.Paper

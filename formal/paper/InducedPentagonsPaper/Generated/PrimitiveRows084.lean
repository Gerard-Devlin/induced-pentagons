import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData084
import InducedPentagonsPaper.Generated.PrimitiveRows076

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_1008 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384701) = [28, 10, 16, 12, 16, 88, 204, 222, 12, 128, 28, 0, 4, 48, 8, 0, 12, 0, 0, 0, 0, 76] := by
  decide +kernel

theorem primitive_host_1008_semantics :
    (Generated.hostChunk084[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[0]).mask = 384701 := by decide +kernel
  have hv : (Generated.hostChunk084[0]).primitive.toList = [28, 10, 16, 12, 16, 88, 204, 222, 12, 128, 28, 0, 4, 48, 8, 0, 12, 0, 0, 0, 0, 76] := by decide +kernel
  rw [hm, hv, primitive_values_1008]
  rfl

theorem primitive_values_1009 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384703) = [30, 10, 18, 16, 18, 104, 282, 282, 16, 190, 48, 0, 0, 72, 12, 0, 16, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_1009_semantics :
    (Generated.hostChunk084[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[1]).mask = 384703 := by decide +kernel
  have hv : (Generated.hostChunk084[1]).primitive.toList = [30, 10, 18, 16, 18, 104, 282, 282, 16, 190, 48, 0, 0, 72, 12, 0, 16, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_1009]
  rfl

theorem primitive_values_1010 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384763) = [30, 0, 0, 0, 0, 102, 258, 276, 0, 162, 60, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 84] := by
  decide +kernel

theorem primitive_host_1010_semantics :
    (Generated.hostChunk084[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[2]).mask = 384763 := by decide +kernel
  have hv : (Generated.hostChunk084[2]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 276, 0, 162, 60, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 84] := by decide +kernel
  rw [hm, hv, primitive_values_1010]
  rfl

theorem primitive_values_1011 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384764) = [28, 0, 0, 0, 0, 86, 186, 216, 0, 106, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_1011_semantics :
    (Generated.hostChunk084[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[3]).mask = 384764 := by decide +kernel
  have hv : (Generated.hostChunk084[3]).primitive.toList = [28, 0, 0, 0, 0, 86, 186, 216, 0, 106, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_1011]
  rfl

theorem primitive_values_1012 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384765) = [30, 0, 0, 0, 0, 102, 258, 278, 0, 166, 48, 0, 4, 48, 0, 0, 0, 0, 0, 0, 0, 96] := by
  decide +kernel

theorem primitive_host_1012_semantics :
    (Generated.hostChunk084[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[4]).mask = 384765 := by decide +kernel
  have hv : (Generated.hostChunk084[4]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 278, 0, 166, 48, 0, 4, 48, 0, 0, 0, 0, 0, 0, 0, 96] := by decide +kernel
  rw [hm, hv, primitive_values_1012]
  rfl

theorem primitive_values_1013 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384767) = [32, 0, 0, 0, 0, 120, 354, 352, 0, 258, 60, 0, 0, 120, 0, 4, 0, 0, 0, 0, 0, 180] := by
  decide +kernel

theorem primitive_host_1013_semantics :
    (Generated.hostChunk084[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[5]).mask = 384767 := by decide +kernel
  have hv : (Generated.hostChunk084[5]).primitive.toList = [32, 0, 0, 0, 0, 120, 354, 352, 0, 258, 60, 0, 0, 120, 0, 4, 0, 0, 0, 0, 0, 180] := by decide +kernel
  rw [hm, hv, primitive_values_1013]
  rfl

theorem primitive_values_1014 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384957) = [30, 0, 0, 0, 0, 104, 276, 288, 0, 196, 24, 0, 0, 120, 0, 16, 0, 0, 0, 0, 0, 144] := by
  decide +kernel

theorem primitive_host_1014_semantics :
    (Generated.hostChunk084[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[6]).mask = 384957 := by decide +kernel
  have hv : (Generated.hostChunk084[6]).primitive.toList = [30, 0, 0, 0, 0, 104, 276, 288, 0, 196, 24, 0, 0, 120, 0, 16, 0, 0, 0, 0, 0, 144] := by decide +kernel
  rw [hm, hv, primitive_values_1014]
  rfl

theorem primitive_values_1015 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384958) = [30, 0, 0, 0, 0, 102, 258, 280, 0, 170, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_1015_semantics :
    (Generated.hostChunk084[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[7]).mask = 384958 := by decide +kernel
  have hv : (Generated.hostChunk084[7]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 280, 0, 170, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_1015]
  rfl

theorem primitive_values_1016 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 384959) = [32, 0, 0, 0, 0, 120, 354, 354, 0, 262, 48, 0, 0, 144, 0, 8, 0, 0, 0, 0, 0, 192] := by
  decide +kernel

theorem primitive_host_1016_semantics :
    (Generated.hostChunk084[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[8]).mask = 384959 := by decide +kernel
  have hv : (Generated.hostChunk084[8]).primitive.toList = [32, 0, 0, 0, 0, 120, 354, 354, 0, 262, 48, 0, 0, 144, 0, 8, 0, 0, 0, 0, 0, 192] := by decide +kernel
  rw [hm, hv, primitive_values_1016]
  rfl

theorem primitive_values_1017 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 385022) = [32, 0, 0, 0, 0, 118, 330, 348, 0, 234, 60, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 156] := by
  decide +kernel

theorem primitive_host_1017_semantics :
    (Generated.hostChunk084[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[9]).mask = 385022 := by decide +kernel
  have hv : (Generated.hostChunk084[9]).primitive.toList = [32, 0, 0, 0, 0, 118, 330, 348, 0, 234, 60, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 156] := by decide +kernel
  rw [hm, hv, primitive_values_1017]
  rfl

theorem primitive_values_1018 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 385023) = [34, 0, 0, 0, 0, 138, 450, 436, 0, 362, 52, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 292] := by
  decide +kernel

theorem primitive_host_1018_semantics :
    (Generated.hostChunk084[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[10]).mask = 385023 := by decide +kernel
  have hv : (Generated.hostChunk084[10]).primitive.toList = [34, 0, 0, 0, 0, 138, 450, 436, 0, 362, 52, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 292] := by decide +kernel
  rw [hm, hv, primitive_values_1018]
  rfl

theorem primitive_values_1019 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 393149) = [32, 0, 0, 0, 0, 118, 330, 352, 0, 242, 36, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 180] := by
  decide +kernel

theorem primitive_host_1019_semantics :
    (Generated.hostChunk084[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk084[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk084[11]).mask = 393149 := by decide +kernel
  have hv : (Generated.hostChunk084[11]).primitive.toList = [32, 0, 0, 0, 0, 118, 330, 352, 0, 242, 36, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 180] := by decide +kernel
  rw [hm, hv, primitive_values_1019]
  rfl

theorem primitive_chunk_084_semantics :
    ∀ h ∈ Generated.hostChunk084.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk084.toList = [Generated.hostChunk084[0], Generated.hostChunk084[1], Generated.hostChunk084[2], Generated.hostChunk084[3], Generated.hostChunk084[4], Generated.hostChunk084[5], Generated.hostChunk084[6], Generated.hostChunk084[7], Generated.hostChunk084[8], Generated.hostChunk084[9], Generated.hostChunk084[10], Generated.hostChunk084[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_1008_semantics
  · exact primitive_host_1009_semantics
  · exact primitive_host_1010_semantics
  · exact primitive_host_1011_semantics
  · exact primitive_host_1012_semantics
  · exact primitive_host_1013_semantics
  · exact primitive_host_1014_semantics
  · exact primitive_host_1015_semantics
  · exact primitive_host_1016_semantics
  · exact primitive_host_1017_semantics
  · exact primitive_host_1018_semantics
  · exact primitive_host_1019_semantics

end InducedPentagons.Paper

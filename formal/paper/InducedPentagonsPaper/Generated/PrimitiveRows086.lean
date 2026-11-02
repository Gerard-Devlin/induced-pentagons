import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData086
import InducedPentagonsPaper.Generated.PrimitiveRows078

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_1032 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 454655) = [34, 0, 0, 0, 0, 136, 432, 428, 0, 336, 64, 0, 0, 192, 0, 4, 0, 0, 0, 0, 0, 256] := by
  decide +kernel

theorem primitive_host_1032_semantics :
    (Generated.hostChunk086[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[0]).mask = 454655 := by decide +kernel
  have hv : (Generated.hostChunk086[0]).primitive.toList = [34, 0, 0, 0, 0, 136, 432, 428, 0, 336, 64, 0, 0, 192, 0, 4, 0, 0, 0, 0, 0, 256] := by decide +kernel
  rw [hm, hv, primitive_values_1032]
  rfl

theorem primitive_values_1033 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 458685) = [32, 0, 0, 0, 0, 116, 312, 342, 0, 212, 60, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 132] := by
  decide +kernel

theorem primitive_host_1033_semantics :
    (Generated.hostChunk086[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[1]).mask = 458685 := by decide +kernel
  have hv : (Generated.hostChunk086[1]).primitive.toList = [32, 0, 0, 0, 0, 116, 312, 342, 0, 212, 60, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 132] := by decide +kernel
  rw [hm, hv, primitive_values_1033]
  rfl

theorem primitive_values_1034 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 458687) = [34, 0, 0, 0, 0, 134, 408, 422, 0, 308, 76, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 220] := by
  decide +kernel

theorem primitive_host_1034_semantics :
    (Generated.hostChunk086[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[2]).mask = 458687 := by decide +kernel
  have hv : (Generated.hostChunk086[2]).primitive.toList = [34, 0, 0, 0, 0, 134, 408, 422, 0, 308, 76, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 220] := by decide +kernel
  rw [hm, hv, primitive_values_1034]
  rfl

theorem primitive_values_1035 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 458751) = [36, 0, 0, 0, 0, 154, 528, 518, 0, 444, 60, 0, 0, 312, 0, 0, 0, 0, 0, 0, 0, 372] := by
  decide +kernel

theorem primitive_host_1035_semantics :
    (Generated.hostChunk086[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[3]).mask = 458751 := by decide +kernel
  have hv : (Generated.hostChunk086[3]).primitive.toList = [36, 0, 0, 0, 0, 154, 528, 518, 0, 444, 60, 0, 0, 312, 0, 0, 0, 0, 0, 0, 0, 372] := by decide +kernel
  rw [hm, hv, primitive_values_1035]
  rfl

theorem primitive_values_1036 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 522111) = [34, 0, 0, 0, 0, 134, 408, 424, 0, 312, 64, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 232] := by
  decide +kernel

theorem primitive_host_1036_semantics :
    (Generated.hostChunk086[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[4]).mask = 522111 := by decide +kernel
  have hv : (Generated.hostChunk086[4]).primitive.toList = [34, 0, 0, 0, 0, 134, 408, 424, 0, 312, 64, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 232] := by decide +kernel
  rw [hm, hv, primitive_values_1036]
  rfl

theorem primitive_values_1037 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 522238) = [34, 0, 0, 0, 0, 132, 384, 416, 0, 280, 88, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 184] := by
  decide +kernel

theorem primitive_host_1037_semantics :
    (Generated.hostChunk086[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[5]).mask = 522238 := by decide +kernel
  have hv : (Generated.hostChunk086[5]).primitive.toList = [34, 0, 0, 0, 0, 132, 384, 416, 0, 280, 88, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 184] := by decide +kernel
  rw [hm, hv, primitive_values_1037]
  rfl

theorem primitive_values_1038 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 522239) = [36, 0, 0, 0, 0, 152, 504, 512, 0, 416, 72, 0, 0, 264, 0, 0, 0, 0, 0, 0, 0, 336] := by
  decide +kernel

theorem primitive_host_1038_semantics :
    (Generated.hostChunk086[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[6]).mask = 522239 := by decide +kernel
  have hv : (Generated.hostChunk086[6]).primitive.toList = [36, 0, 0, 0, 0, 152, 504, 512, 0, 416, 72, 0, 0, 264, 0, 0, 0, 0, 0, 0, 0, 336] := by decide +kernel
  rw [hm, hv, primitive_values_1038]
  rfl

theorem primitive_values_1039 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 524287) = [38, 0, 0, 0, 0, 172, 624, 616, 0, 560, 48, 0, 0, 456, 0, 0, 0, 0, 0, 0, 0, 504] := by
  decide +kernel

theorem primitive_host_1039_semantics :
    (Generated.hostChunk086[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[7]).mask = 524287 := by decide +kernel
  have hv : (Generated.hostChunk086[7]).primitive.toList = [38, 0, 0, 0, 0, 172, 624, 616, 0, 560, 48, 0, 0, 456, 0, 0, 0, 0, 0, 0, 0, 504] := by decide +kernel
  rw [hm, hv, primitive_values_1039]
  rfl

theorem primitive_values_1040 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1015743) = [36, 0, 0, 0, 0, 150, 480, 504, 0, 384, 96, 0, 0, 192, 0, 0, 0, 0, 0, 0, 0, 288] := by
  decide +kernel

theorem primitive_host_1040_semantics :
    (Generated.hostChunk086[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[8]).mask = 1015743 := by decide +kernel
  have hv : (Generated.hostChunk086[8]).primitive.toList = [36, 0, 0, 0, 0, 150, 480, 504, 0, 384, 96, 0, 0, 192, 0, 0, 0, 0, 0, 0, 0, 288] := by decide +kernel
  rw [hm, hv, primitive_values_1040]
  rfl

theorem primitive_values_1041 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1015807) = [38, 0, 0, 0, 0, 170, 600, 608, 0, 528, 72, 0, 0, 384, 0, 0, 0, 0, 0, 0, 0, 456] := by
  decide +kernel

theorem primitive_host_1041_semantics :
    (Generated.hostChunk086[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[9]).mask = 1015807 := by decide +kernel
  have hv : (Generated.hostChunk086[9]).primitive.toList = [38, 0, 0, 0, 0, 170, 600, 608, 0, 528, 72, 0, 0, 384, 0, 0, 0, 0, 0, 0, 0, 456] := by decide +kernel
  rw [hm, hv, primitive_values_1041]
  rfl

theorem primitive_values_1042 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 1048575) = [40, 0, 0, 0, 0, 190, 720, 720, 0, 680, 40, 0, 0, 600, 0, 0, 0, 0, 0, 0, 0, 640] := by
  decide +kernel

theorem primitive_host_1042_semantics :
    (Generated.hostChunk086[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[10]).mask = 1048575 := by decide +kernel
  have hv : (Generated.hostChunk086[10]).primitive.toList = [40, 0, 0, 0, 0, 190, 720, 720, 0, 680, 40, 0, 0, 600, 0, 0, 0, 0, 0, 0, 0, 640] := by decide +kernel
  rw [hm, hv, primitive_values_1042]
  rfl

theorem primitive_values_1043 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2097151) = [42, 0, 0, 0, 0, 210, 840, 840, 0, 840, 0, 0, 0, 840, 0, 0, 0, 0, 0, 0, 0, 840] := by
  decide +kernel

theorem primitive_host_1043_semantics :
    (Generated.hostChunk086[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[11]).mask = 2097151 := by decide +kernel
  have hv : (Generated.hostChunk086[11]).primitive.toList = [42, 0, 0, 0, 0, 210, 840, 840, 0, 840, 0, 0, 0, 840, 0, 0, 0, 0, 0, 0, 0, 840] := by decide +kernel
  rw [hm, hv, primitive_values_1043]
  rfl

theorem primitive_chunk_086_semantics :
    ∀ h ∈ Generated.hostChunk086.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk086.toList = [Generated.hostChunk086[0], Generated.hostChunk086[1], Generated.hostChunk086[2], Generated.hostChunk086[3], Generated.hostChunk086[4], Generated.hostChunk086[5], Generated.hostChunk086[6], Generated.hostChunk086[7], Generated.hostChunk086[8], Generated.hostChunk086[9], Generated.hostChunk086[10], Generated.hostChunk086[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_1032_semantics
  · exact primitive_host_1033_semantics
  · exact primitive_host_1034_semantics
  · exact primitive_host_1035_semantics
  · exact primitive_host_1036_semantics
  · exact primitive_host_1037_semantics
  · exact primitive_host_1038_semantics
  · exact primitive_host_1039_semantics
  · exact primitive_host_1040_semantics
  · exact primitive_host_1041_semantics
  · exact primitive_host_1042_semantics
  · exact primitive_host_1043_semantics

end InducedPentagons.Paper

import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData077
import InducedPentagonsPaper.Generated.PrimitiveRows069

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0924 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 129023) = [32, 0, 0, 0, 0, 122, 378, 360, 0, 268, 68, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 188] := by
  decide +kernel

theorem primitive_host_0924_semantics :
    (Generated.hostChunk077[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[0]).mask = 129023 := by decide +kernel
  have hv : (Generated.hostChunk077[0]).primitive.toList = [32, 0, 0, 0, 0, 122, 378, 360, 0, 268, 68, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 188] := by decide +kernel
  rw [hm, hv, primitive_values_0924]
  rfl

theorem primitive_values_0925 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 131004) = [28, 0, 0, 0, 0, 86, 186, 228, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0925_semantics :
    (Generated.hostChunk077[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[1]).mask = 131004 := by decide +kernel
  have hv : (Generated.hostChunk077[1]).primitive.toList = [28, 0, 0, 0, 0, 86, 186, 228, 0, 84, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0925]
  rfl

theorem primitive_values_0926 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 131005) = [30, 0, 0, 0, 0, 102, 258, 284, 0, 156, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by
  decide +kernel

theorem primitive_host_0926_semantics :
    (Generated.hostChunk077[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[2]).mask = 131005 := by decide +kernel
  have hv : (Generated.hostChunk077[2]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 284, 0, 156, 44, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 92] := by decide +kernel
  rw [hm, hv, primitive_values_0926]
  rfl

theorem primitive_values_0927 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 131007) = [32, 0, 0, 0, 0, 120, 354, 356, 0, 244, 68, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 164] := by
  decide +kernel

theorem primitive_host_0927_semantics :
    (Generated.hostChunk077[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[3]).mask = 131007 := by decide +kernel
  have hv : (Generated.hostChunk077[3]).primitive.toList = [32, 0, 0, 0, 0, 120, 354, 356, 0, 244, 68, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 164] := by decide +kernel
  rw [hm, hv, primitive_values_0927]
  rfl

theorem primitive_values_0928 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 131071) = [34, 0, 0, 0, 0, 140, 474, 444, 0, 372, 60, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 300] := by
  decide +kernel

theorem primitive_host_0928_semantics :
    (Generated.hostChunk077[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[4]).mask = 131071 := by decide +kernel
  have hv : (Generated.hostChunk077[4]).primitive.toList = [34, 0, 0, 0, 0, 140, 474, 444, 0, 372, 60, 0, 0, 240, 0, 0, 0, 0, 0, 0, 0, 300] := by decide +kernel
  rw [hm, hv, primitive_values_0928]
  rfl

theorem primitive_values_0929 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 259903) = [30, 0, 0, 0, 0, 102, 264, 288, 0, 144, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0929_semantics :
    (Generated.hostChunk077[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[5]).mask = 259903 := by decide +kernel
  have hv : (Generated.hostChunk077[5]).primitive.toList = [30, 0, 0, 0, 0, 102, 264, 288, 0, 144, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0929]
  rfl

theorem primitive_values_0930 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 259963) = [30, 0, 0, 0, 0, 102, 258, 288, 0, 162, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0930_semantics :
    (Generated.hostChunk077[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[6]).mask = 259963 := by decide +kernel
  have hv : (Generated.hostChunk077[6]).primitive.toList = [30, 0, 0, 0, 0, 102, 258, 288, 0, 162, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0930]
  rfl

theorem primitive_values_0931 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 259964) = [28, 0, 0, 0, 0, 84, 168, 216, 0, 72, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0931_semantics :
    (Generated.hostChunk077[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[7]).mask = 259964 := by decide +kernel
  have hv : (Generated.hostChunk077[7]).primitive.toList = [28, 0, 0, 0, 0, 84, 168, 216, 0, 72, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0931]
  rfl

theorem primitive_values_0932 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 259965) = [30, 0, 0, 0, 0, 100, 240, 278, 0, 132, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0932_semantics :
    (Generated.hostChunk077[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[8]).mask = 259965 := by decide +kernel
  have hv : (Generated.hostChunk077[8]).primitive.toList = [30, 0, 0, 0, 0, 100, 240, 278, 0, 132, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0932]
  rfl

theorem primitive_values_0933 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 259967) = [32, 0, 0, 0, 0, 118, 336, 352, 0, 224, 72, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 144] := by
  decide +kernel

theorem primitive_host_0933_semantics :
    (Generated.hostChunk077[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[9]).mask = 259967 := by decide +kernel
  have hv : (Generated.hostChunk077[9]).primitive.toList = [32, 0, 0, 0, 0, 118, 336, 352, 0, 224, 72, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 144] := by decide +kernel
  rw [hm, hv, primitive_values_0933]
  rfl

theorem primitive_values_0934 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 260094) = [32, 0, 0, 0, 0, 116, 312, 344, 0, 192, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96] := by
  decide +kernel

theorem primitive_host_0934_semantics :
    (Generated.hostChunk077[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[10]).mask = 260094 := by decide +kernel
  have hv : (Generated.hostChunk077[10]).primitive.toList = [32, 0, 0, 0, 0, 116, 312, 344, 0, 192, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96] := by decide +kernel
  rw [hm, hv, primitive_values_0934]
  rfl

theorem primitive_values_0935 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 260095) = [34, 0, 0, 0, 0, 136, 432, 432, 0, 320, 88, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 232] := by
  decide +kernel

theorem primitive_host_0935_semantics :
    (Generated.hostChunk077[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk077[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk077[11]).mask = 260095 := by decide +kernel
  have hv : (Generated.hostChunk077[11]).primitive.toList = [34, 0, 0, 0, 0, 136, 432, 432, 0, 320, 88, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 232] := by decide +kernel
  rw [hm, hv, primitive_values_0935]
  rfl

theorem primitive_chunk_077_semantics :
    ∀ h ∈ Generated.hostChunk077.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk077.toList = [Generated.hostChunk077[0], Generated.hostChunk077[1], Generated.hostChunk077[2], Generated.hostChunk077[3], Generated.hostChunk077[4], Generated.hostChunk077[5], Generated.hostChunk077[6], Generated.hostChunk077[7], Generated.hostChunk077[8], Generated.hostChunk077[9], Generated.hostChunk077[10], Generated.hostChunk077[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0924_semantics
  · exact primitive_host_0925_semantics
  · exact primitive_host_0926_semantics
  · exact primitive_host_0927_semantics
  · exact primitive_host_0928_semantics
  · exact primitive_host_0929_semantics
  · exact primitive_host_0930_semantics
  · exact primitive_host_0931_semantics
  · exact primitive_host_0932_semantics
  · exact primitive_host_0933_semantics
  · exact primitive_host_0934_semantics
  · exact primitive_host_0935_semantics

end InducedPentagons.Paper

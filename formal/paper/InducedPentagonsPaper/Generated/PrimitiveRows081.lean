import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData081
import InducedPentagonsPaper.Generated.PrimitiveRows073

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0972 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376830) = [32, 0, 0, 0, 0, 122, 360, 368, 0, 288, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by
  decide +kernel

theorem primitive_host_0972_semantics :
    (Generated.hostChunk081[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[0]).mask = 376830 := by decide +kernel
  have hv : (Generated.hostChunk081[0]).primitive.toList = [32, 0, 0, 0, 0, 122, 360, 368, 0, 288, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by decide +kernel
  rw [hm, hv, primitive_values_0972]
  rfl

theorem primitive_values_0973 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376831) = [34, 0, 0, 0, 0, 142, 480, 456, 0, 416, 16, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 376] := by
  decide +kernel

theorem primitive_host_0973_semantics :
    (Generated.hostChunk081[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[1]).mask = 376831 := by decide +kernel
  have hv : (Generated.hostChunk081[1]).primitive.toList = [34, 0, 0, 0, 0, 142, 480, 456, 0, 416, 16, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 376] := by decide +kernel
  rw [hm, hv, primitive_values_0973]
  rfl

theorem primitive_values_0974 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 377983) = [24, 0, 0, 0, 0, 66, 156, 120, 0, 84, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0974_semantics :
    (Generated.hostChunk081[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[2]).mask = 377983 := by decide +kernel
  have hv : (Generated.hostChunk081[2]).primitive.toList = [24, 0, 0, 0, 0, 66, 156, 120, 0, 84, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0974]
  rfl

theorem primitive_values_0975 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378106) = [22, 40, 48, 16, 0, 48, 60, 80, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0975_semantics :
    (Generated.hostChunk081[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[3]).mask = 378106 := by decide +kernel
  have hv : (Generated.hostChunk081[3]).primitive.toList = [22, 40, 48, 16, 0, 48, 60, 80, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0975]
  rfl

theorem primitive_values_0976 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378107) = [24, 0, 0, 0, 0, 62, 114, 120, 0, 58, 4, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0976_semantics :
    (Generated.hostChunk081[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[4]).mask = 378107 := by decide +kernel
  have hv : (Generated.hostChunk081[4]).primitive.toList = [24, 0, 0, 0, 0, 62, 114, 120, 0, 58, 4, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0976]
  rfl

theorem primitive_values_0977 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378111) = [26, 0, 0, 0, 0, 78, 192, 168, 0, 112, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0977_semantics :
    (Generated.hostChunk081[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[5]).mask = 378111 := by decide +kernel
  have hv : (Generated.hostChunk081[5]).primitive.toList = [26, 0, 0, 0, 0, 78, 192, 168, 0, 112, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0977]
  rfl

theorem primitive_values_0978 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378358) = [24, 20, 28, 16, 0, 60, 96, 118, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0978_semantics :
    (Generated.hostChunk081[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[6]).mask = 378358 := by decide +kernel
  have hv : (Generated.hostChunk081[6]).primitive.toList = [24, 20, 28, 16, 0, 60, 96, 118, 0, 44, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0978]
  rfl

theorem primitive_values_0979 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378359) = [26, 0, 0, 0, 0, 76, 168, 168, 0, 96, 24, 0, 8, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0979_semantics :
    (Generated.hostChunk081[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[7]).mask = 378359 := by decide +kernel
  have hv : (Generated.hostChunk081[7]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 168, 0, 96, 24, 0, 8, 24, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0979]
  rfl

theorem primitive_values_0980 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378366) = [26, 0, 0, 0, 0, 74, 150, 164, 0, 78, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0980_semantics :
    (Generated.hostChunk081[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[8]).mask = 378366 := by decide +kernel
  have hv : (Generated.hostChunk081[8]).primitive.toList = [26, 0, 0, 0, 0, 74, 150, 164, 0, 78, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0980]
  rfl

theorem primitive_values_0981 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378367) = [28, 0, 0, 0, 0, 92, 246, 224, 0, 158, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0981_semantics :
    (Generated.hostChunk081[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[9]).mask = 378367 := by decide +kernel
  have hv : (Generated.hostChunk081[9]).primitive.toList = [28, 0, 0, 0, 0, 92, 246, 224, 0, 158, 28, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0981]
  rfl

theorem primitive_values_0982 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378878) = [28, 0, 0, 0, 0, 88, 204, 216, 0, 116, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by
  decide +kernel

theorem primitive_host_0982_semantics :
    (Generated.hostChunk081[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[10]).mask = 378878 := by decide +kernel
  have hv : (Generated.hostChunk081[10]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 216, 0, 116, 16, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 64] := by decide +kernel
  rw [hm, hv, primitive_values_0982]
  rfl

theorem primitive_values_0983 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 378879) = [30, 0, 0, 0, 0, 108, 324, 288, 0, 228, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0983_semantics :
    (Generated.hostChunk081[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk081[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk081[11]).mask = 378879 := by decide +kernel
  have hv : (Generated.hostChunk081[11]).primitive.toList = [30, 0, 0, 0, 0, 108, 324, 288, 0, 228, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0983]
  rfl

theorem primitive_chunk_081_semantics :
    ∀ h ∈ Generated.hostChunk081.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk081.toList = [Generated.hostChunk081[0], Generated.hostChunk081[1], Generated.hostChunk081[2], Generated.hostChunk081[3], Generated.hostChunk081[4], Generated.hostChunk081[5], Generated.hostChunk081[6], Generated.hostChunk081[7], Generated.hostChunk081[8], Generated.hostChunk081[9], Generated.hostChunk081[10], Generated.hostChunk081[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0972_semantics
  · exact primitive_host_0973_semantics
  · exact primitive_host_0974_semantics
  · exact primitive_host_0975_semantics
  · exact primitive_host_0976_semantics
  · exact primitive_host_0977_semantics
  · exact primitive_host_0978_semantics
  · exact primitive_host_0979_semantics
  · exact primitive_host_0980_semantics
  · exact primitive_host_0981_semantics
  · exact primitive_host_0982_semantics
  · exact primitive_host_0983_semantics

end InducedPentagons.Paper

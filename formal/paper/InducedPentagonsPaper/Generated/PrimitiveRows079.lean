import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData079
import InducedPentagonsPaper.Generated.PrimitiveRows071

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0948 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375871) = [26, 0, 0, 0, 0, 82, 216, 184, 0, 152, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0948_semantics :
    (Generated.hostChunk079[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[0]).mask = 375871 := by decide +kernel
  have hv : (Generated.hostChunk079[0]).primitive.toList = [26, 0, 0, 0, 0, 82, 216, 184, 0, 152, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0948]
  rfl

theorem primitive_values_0949 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375907) = [22, 0, 0, 0, 0, 52, 90, 84, 0, 50, 4, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 28] := by
  decide +kernel

theorem primitive_host_0949_semantics :
    (Generated.hostChunk079[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[1]).mask = 375907 := by decide +kernel
  have hv : (Generated.hostChunk079[1]).primitive.toList = [22, 0, 0, 0, 0, 52, 90, 84, 0, 50, 4, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 28] := by decide +kernel
  rw [hm, hv, primitive_values_0949]
  rfl

theorem primitive_values_0950 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375909) = [22, 0, 0, 0, 0, 50, 72, 84, 0, 40, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0950_semantics :
    (Generated.hostChunk079[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[2]).mask = 375909 := by decide +kernel
  have hv : (Generated.hostChunk079[2]).primitive.toList = [22, 0, 0, 0, 0, 50, 72, 84, 0, 40, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0950]
  rfl

theorem primitive_values_0951 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375911) = [24, 0, 0, 0, 0, 64, 126, 126, 0, 74, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0951_semantics :
    (Generated.hostChunk079[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[3]).mask = 375911 := by decide +kernel
  have hv : (Generated.hostChunk079[3]).primitive.toList = [24, 0, 0, 0, 0, 64, 126, 126, 0, 74, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0951]
  rfl

theorem primitive_values_0952 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375917) = [24, 0, 0, 0, 0, 62, 108, 124, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0952_semantics :
    (Generated.hostChunk079[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[4]).mask = 375917 := by decide +kernel
  have hv : (Generated.hostChunk079[4]).primitive.toList = [24, 0, 0, 0, 0, 62, 108, 124, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0952]
  rfl

theorem primitive_values_0953 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375919) = [26, 0, 0, 0, 0, 78, 180, 176, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0953_semantics :
    (Generated.hostChunk079[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[5]).mask = 375919 := by decide +kernel
  have hv : (Generated.hostChunk079[5]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 176, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0953]
  rfl

theorem primitive_values_0954 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375932) = [24, 30, 36, 36, 36, 64, 120, 134, 36, 84, 12, 0, 0, 48, 24, 0, 36, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0954_semantics :
    (Generated.hostChunk079[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[6]).mask = 375932 := by decide +kernel
  have hv : (Generated.hostChunk079[6]).primitive.toList = [24, 30, 36, 36, 36, 64, 120, 134, 36, 84, 12, 0, 0, 48, 24, 0, 36, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0954]
  rfl

theorem primitive_values_0955 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375933) = [26, 0, 0, 0, 0, 76, 162, 172, 0, 98, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0955_semantics :
    (Generated.hostChunk079[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[7]).mask = 375933 := by decide +kernel
  have hv : (Generated.hostChunk079[7]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 172, 0, 98, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0955]
  rfl

theorem primitive_values_0956 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375934) = [26, 0, 0, 0, 0, 80, 192, 188, 0, 144, 0, 0, 0, 120, 0, 12, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0956_semantics :
    (Generated.hostChunk079[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[8]).mask = 375934 := by decide +kernel
  have hv : (Generated.hostChunk079[8]).primitive.toList = [26, 0, 0, 0, 0, 80, 192, 188, 0, 144, 0, 0, 0, 120, 0, 12, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0956]
  rfl

theorem primitive_values_0957 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375935) = [28, 0, 0, 0, 0, 94, 258, 234, 0, 182, 16, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 136] := by
  decide +kernel

theorem primitive_host_0957_semantics :
    (Generated.hostChunk079[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[9]).mask = 375935 := by decide +kernel
  have hv : (Generated.hostChunk079[9]).primitive.toList = [28, 0, 0, 0, 0, 94, 258, 234, 0, 182, 16, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 136] := by decide +kernel
  rw [hm, hv, primitive_values_0957]
  rfl

theorem primitive_values_0958 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376039) = [26, 0, 0, 0, 0, 78, 180, 176, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0958_semantics :
    (Generated.hostChunk079[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[10]).mask = 376039 := by decide +kernel
  have hv : (Generated.hostChunk079[10]).primitive.toList = [26, 0, 0, 0, 0, 78, 180, 176, 0, 116, 24, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0958]
  rfl

theorem primitive_values_0959 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376043) = [26, 0, 0, 0, 0, 76, 162, 172, 0, 98, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0959_semantics :
    (Generated.hostChunk079[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk079[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk079[11]).mask = 376043 := by decide +kernel
  have hv : (Generated.hostChunk079[11]).primitive.toList = [26, 0, 0, 0, 0, 76, 162, 172, 0, 98, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0959]
  rfl

theorem primitive_chunk_079_semantics :
    ∀ h ∈ Generated.hostChunk079.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk079.toList = [Generated.hostChunk079[0], Generated.hostChunk079[1], Generated.hostChunk079[2], Generated.hostChunk079[3], Generated.hostChunk079[4], Generated.hostChunk079[5], Generated.hostChunk079[6], Generated.hostChunk079[7], Generated.hostChunk079[8], Generated.hostChunk079[9], Generated.hostChunk079[10], Generated.hostChunk079[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0948_semantics
  · exact primitive_host_0949_semantics
  · exact primitive_host_0950_semantics
  · exact primitive_host_0951_semantics
  · exact primitive_host_0952_semantics
  · exact primitive_host_0953_semantics
  · exact primitive_host_0954_semantics
  · exact primitive_host_0955_semantics
  · exact primitive_host_0956_semantics
  · exact primitive_host_0957_semantics
  · exact primitive_host_0958_semantics
  · exact primitive_host_0959_semantics

end InducedPentagons.Paper

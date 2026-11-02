import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData080
import InducedPentagonsPaper.Generated.PrimitiveRows072

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0960 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376047) = [28, 0, 0, 0, 0, 92, 234, 232, 0, 162, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0960_semantics :
    (Generated.hostChunk080[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[0]).mask = 376047 := by decide +kernel
  have hv : (Generated.hostChunk080[0]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 232, 0, 162, 36, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0960]
  rfl

theorem primitive_values_0961 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376056) = [24, 40, 48, 32, 48, 62, 108, 128, 32, 68, 16, 0, 0, 24, 16, 0, 32, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0961_semantics :
    (Generated.hostChunk080[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[1]).mask = 376056 := by decide +kernel
  have hv : (Generated.hostChunk080[1]).primitive.toList = [24, 40, 48, 32, 48, 62, 108, 128, 32, 68, 16, 0, 0, 24, 16, 0, 32, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0961]
  rfl

theorem primitive_values_0962 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376057) = [26, 0, 0, 0, 0, 74, 144, 168, 0, 80, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by
  decide +kernel

theorem primitive_host_0962_semantics :
    (Generated.hostChunk080[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[2]).mask = 376057 := by decide +kernel
  have hv : (Generated.hostChunk080[2]).primitive.toList = [26, 0, 0, 0, 0, 74, 144, 168, 0, 80, 16, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 40] := by decide +kernel
  rw [hm, hv, primitive_values_0962]
  rfl

theorem primitive_values_0963 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376058) = [26, 20, 28, 24, 28, 76, 162, 176, 24, 106, 20, 0, 0, 48, 16, 0, 24, 0, 0, 0, 0, 68] := by
  decide +kernel

theorem primitive_host_0963_semantics :
    (Generated.hostChunk080[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[3]).mask = 376058 := by decide +kernel
  have hv : (Generated.hostChunk080[3]).primitive.toList = [26, 20, 28, 24, 28, 76, 162, 176, 24, 106, 20, 0, 0, 48, 16, 0, 24, 0, 0, 0, 0, 68] := by decide +kernel
  rw [hm, hv, primitive_values_0963]
  rfl

theorem primitive_values_0964 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376059) = [28, 0, 0, 0, 0, 90, 216, 226, 0, 140, 36, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84] := by
  decide +kernel

theorem primitive_host_0964_semantics :
    (Generated.hostChunk080[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[4]).mask = 376059 := by decide +kernel
  have hv : (Generated.hostChunk080[4]).primitive.toList = [28, 0, 0, 0, 0, 90, 216, 226, 0, 140, 36, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84] := by decide +kernel
  rw [hm, hv, primitive_values_0964]
  rfl

theorem primitive_values_0965 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376062) = [28, 0, 0, 0, 0, 92, 234, 236, 0, 170, 12, 0, 0, 120, 0, 16, 0, 0, 0, 0, 0, 132] := by
  decide +kernel

theorem primitive_host_0965_semantics :
    (Generated.hostChunk080[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[5]).mask = 376062 := by decide +kernel
  have hv : (Generated.hostChunk080[5]).primitive.toList = [28, 0, 0, 0, 0, 92, 234, 236, 0, 170, 12, 0, 0, 120, 0, 16, 0, 0, 0, 0, 0, 132] := by decide +kernel
  rw [hm, hv, primitive_values_0965]
  rfl

theorem primitive_values_0966 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376063) = [30, 0, 0, 0, 0, 108, 312, 296, 0, 232, 32, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 176] := by
  decide +kernel

theorem primitive_host_0966_semantics :
    (Generated.hostChunk080[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[6]).mask = 376063 := by decide +kernel
  have hv : (Generated.hostChunk080[6]).primitive.toList = [30, 0, 0, 0, 0, 108, 312, 296, 0, 232, 32, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 176] := by decide +kernel
  rw [hm, hv, primitive_values_0966]
  rfl

theorem primitive_values_0967 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376303) = [30, 0, 0, 0, 0, 108, 306, 300, 0, 234, 36, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 180] := by
  decide +kernel

theorem primitive_host_0967_semantics :
    (Generated.hostChunk080[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[7]).mask = 376303 := by decide +kernel
  have hv : (Generated.hostChunk080[7]).primitive.toList = [30, 0, 0, 0, 0, 108, 306, 300, 0, 234, 36, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 180] := by decide +kernel
  rw [hm, hv, primitive_values_0967]
  rfl

theorem primitive_values_0968 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376310) = [28, 10, 16, 16, 16, 90, 216, 230, 16, 148, 28, 0, 0, 72, 12, 0, 16, 0, 0, 0, 0, 100] := by
  decide +kernel

theorem primitive_host_0968_semantics :
    (Generated.hostChunk080[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[8]).mask = 376310 := by decide +kernel
  have hv : (Generated.hostChunk080[8]).primitive.toList = [28, 10, 16, 16, 16, 90, 216, 230, 16, 148, 28, 0, 0, 72, 12, 0, 16, 0, 0, 0, 0, 100] := by decide +kernel
  rw [hm, hv, primitive_values_0968]
  rfl

theorem primitive_values_0969 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376311) = [30, 0, 0, 0, 0, 106, 288, 292, 0, 208, 48, 0, 0, 96, 0, 4, 0, 0, 0, 0, 0, 144] := by
  decide +kernel

theorem primitive_host_0969_semantics :
    (Generated.hostChunk080[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[9]).mask = 376311 := by decide +kernel
  have hv : (Generated.hostChunk080[9]).primitive.toList = [30, 0, 0, 0, 0, 106, 288, 292, 0, 208, 48, 0, 0, 96, 0, 4, 0, 0, 0, 0, 0, 144] := by decide +kernel
  rw [hm, hv, primitive_values_0969]
  rfl

theorem primitive_values_0970 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376318) = [30, 0, 0, 0, 0, 106, 288, 296, 0, 216, 24, 0, 0, 144, 0, 12, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0970_semantics :
    (Generated.hostChunk080[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[10]).mask = 376318 := by decide +kernel
  have hv : (Generated.hostChunk080[10]).primitive.toList = [30, 0, 0, 0, 0, 106, 288, 296, 0, 216, 24, 0, 0, 144, 0, 12, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0970]
  rfl

theorem primitive_values_0971 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 376319) = [32, 0, 0, 0, 0, 124, 384, 370, 0, 308, 36, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 252] := by
  decide +kernel

theorem primitive_host_0971_semantics :
    (Generated.hostChunk080[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk080[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk080[11]).mask = 376319 := by decide +kernel
  have hv : (Generated.hostChunk080[11]).primitive.toList = [32, 0, 0, 0, 0, 124, 384, 370, 0, 308, 36, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 252] := by decide +kernel
  rw [hm, hv, primitive_values_0971]
  rfl

theorem primitive_chunk_080_semantics :
    ∀ h ∈ Generated.hostChunk080.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk080.toList = [Generated.hostChunk080[0], Generated.hostChunk080[1], Generated.hostChunk080[2], Generated.hostChunk080[3], Generated.hostChunk080[4], Generated.hostChunk080[5], Generated.hostChunk080[6], Generated.hostChunk080[7], Generated.hostChunk080[8], Generated.hostChunk080[9], Generated.hostChunk080[10], Generated.hostChunk080[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0960_semantics
  · exact primitive_host_0961_semantics
  · exact primitive_host_0962_semantics
  · exact primitive_host_0963_semantics
  · exact primitive_host_0964_semantics
  · exact primitive_host_0965_semantics
  · exact primitive_host_0966_semantics
  · exact primitive_host_0967_semantics
  · exact primitive_host_0968_semantics
  · exact primitive_host_0969_semantics
  · exact primitive_host_0970_semantics
  · exact primitive_host_0971_semantics

end InducedPentagons.Paper

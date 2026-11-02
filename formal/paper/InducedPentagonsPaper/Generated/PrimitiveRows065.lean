import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData065
import InducedPentagonsPaper.Generated.PrimitiveRows057

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0780 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61373) = [26, 0, 0, 0, 0, 76, 168, 180, 0, 82, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by
  decide +kernel

theorem primitive_host_0780_semantics :
    (Generated.hostChunk065[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[0]).mask = 61373 := by decide +kernel
  have hv : (Generated.hostChunk065[0]).primitive.toList = [26, 0, 0, 0, 0, 76, 168, 180, 0, 82, 20, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44] := by decide +kernel
  rw [hm, hv, primitive_values_0780]
  rfl

theorem primitive_values_0781 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61374) = [26, 0, 0, 0, 0, 74, 150, 174, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0781_semantics :
    (Generated.hostChunk065[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[1]).mask = 61374 := by decide +kernel
  have hv : (Generated.hostChunk065[1]).primitive.toList = [26, 0, 0, 0, 0, 74, 150, 174, 0, 60, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0781]
  rfl

theorem primitive_values_0782 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61375) = [28, 0, 0, 0, 0, 92, 246, 232, 0, 136, 48, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 72] := by
  decide +kernel

theorem primitive_host_0782_semantics :
    (Generated.hostChunk065[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[2]).mask = 61375 := by decide +kernel
  have hv : (Generated.hostChunk065[2]).primitive.toList = [28, 0, 0, 0, 0, 92, 246, 232, 0, 136, 48, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 72] := by decide +kernel
  rw [hm, hv, primitive_values_0782]
  rfl

theorem primitive_values_0783 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61438) = [28, 0, 0, 0, 0, 90, 222, 228, 0, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0783_semantics :
    (Generated.hostChunk065[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[3]).mask = 61438 := by decide +kernel
  have hv : (Generated.hostChunk065[3]).primitive.toList = [28, 0, 0, 0, 0, 90, 222, 228, 0, 112, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0783]
  rfl

theorem primitive_values_0784 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 61439) = [30, 0, 0, 0, 0, 110, 342, 300, 0, 224, 56, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 152] := by
  decide +kernel

theorem primitive_host_0784_semantics :
    (Generated.hostChunk065[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[4]).mask = 61439 := by decide +kernel
  have hv : (Generated.hostChunk065[4]).primitive.toList = [30, 0, 0, 0, 0, 110, 342, 300, 0, 224, 56, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 152] := by decide +kernel
  rw [hm, hv, primitive_values_0784]
  rfl

theorem primitive_values_0785 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 65468) = [26, 0, 0, 0, 0, 72, 132, 180, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0785_semantics :
    (Generated.hostChunk065[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[5]).mask = 65468 := by decide +kernel
  have hv : (Generated.hostChunk065[5]).primitive.toList = [26, 0, 0, 0, 0, 72, 132, 180, 0, 36, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0785]
  rfl

theorem primitive_values_0786 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 65469) = [28, 0, 0, 0, 0, 88, 204, 228, 0, 100, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by
  decide +kernel

theorem primitive_host_0786_semantics :
    (Generated.hostChunk065[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[6]).mask = 65469 := by decide +kernel
  have hv : (Generated.hostChunk065[6]).primitive.toList = [28, 0, 0, 0, 0, 88, 204, 228, 0, 100, 28, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 52] := by decide +kernel
  rw [hm, hv, primitive_values_0786]
  rfl

theorem primitive_values_0787 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 65471) = [30, 0, 0, 0, 0, 106, 300, 292, 0, 180, 60, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 108] := by
  decide +kernel

theorem primitive_host_0787_semantics :
    (Generated.hostChunk065[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[7]).mask = 65471 := by decide +kernel
  have hv : (Generated.hostChunk065[7]).primitive.toList = [30, 0, 0, 0, 0, 106, 300, 292, 0, 180, 60, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 108] := by decide +kernel
  rw [hm, hv, primitive_values_0787]
  rfl

theorem primitive_values_0788 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 65535) = [32, 0, 0, 0, 0, 126, 420, 372, 0, 300, 60, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 228] := by
  decide +kernel

theorem primitive_host_0788_semantics :
    (Generated.hostChunk065[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[8]).mask = 65535 := by decide +kernel
  have hv : (Generated.hostChunk065[8]).primitive.toList = [32, 0, 0, 0, 0, 126, 420, 372, 0, 300, 60, 0, 0, 168, 0, 0, 0, 0, 0, 0, 0, 228] := by decide +kernel
  rw [hm, hv, primitive_values_0788]
  rfl

theorem primitive_values_0789 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111582) = [24, 0, 0, 0, 0, 72, 144, 168, 0, 96, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by
  decide +kernel

theorem primitive_host_0789_semantics :
    (Generated.hostChunk065[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[9]).mask = 111582 := by decide +kernel
  have hv : (Generated.hostChunk065[9]).primitive.toList = [24, 0, 0, 0, 0, 72, 144, 168, 0, 96, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48] := by decide +kernel
  rw [hm, hv, primitive_values_0789]
  rfl

theorem primitive_values_0790 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111583) = [26, 0, 0, 0, 0, 88, 216, 224, 0, 176, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by
  decide +kernel

theorem primitive_host_0790_semantics :
    (Generated.hostChunk065[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[10]).mask = 111583 := by decide +kernel
  have hv : (Generated.hostChunk065[10]).primitive.toList = [26, 0, 0, 0, 0, 88, 216, 224, 0, 176, 40, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 136] := by decide +kernel
  rw [hm, hv, primitive_values_0790]
  rfl

theorem primitive_values_0791 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 111594) = [22, 0, 0, 0, 0, 54, 90, 104, 0, 50, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0791_semantics :
    (Generated.hostChunk065[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk065[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk065[11]).mask = 111594 := by decide +kernel
  have hv : (Generated.hostChunk065[11]).primitive.toList = [22, 0, 0, 0, 0, 54, 90, 104, 0, 50, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0791]
  rfl

theorem primitive_chunk_065_semantics :
    ∀ h ∈ Generated.hostChunk065.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk065.toList = [Generated.hostChunk065[0], Generated.hostChunk065[1], Generated.hostChunk065[2], Generated.hostChunk065[3], Generated.hostChunk065[4], Generated.hostChunk065[5], Generated.hostChunk065[6], Generated.hostChunk065[7], Generated.hostChunk065[8], Generated.hostChunk065[9], Generated.hostChunk065[10], Generated.hostChunk065[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0780_semantics
  · exact primitive_host_0781_semantics
  · exact primitive_host_0782_semantics
  · exact primitive_host_0783_semantics
  · exact primitive_host_0784_semantics
  · exact primitive_host_0785_semantics
  · exact primitive_host_0786_semantics
  · exact primitive_host_0787_semantics
  · exact primitive_host_0788_semantics
  · exact primitive_host_0789_semantics
  · exact primitive_host_0790_semantics
  · exact primitive_host_0791_semantics

end InducedPentagons.Paper

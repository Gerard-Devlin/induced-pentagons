import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData078
import InducedPentagonsPaper.Generated.PrimitiveRows070

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0936 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 262143) = [36, 0, 0, 0, 0, 156, 552, 528, 0, 456, 72, 0, 0, 312, 0, 0, 0, 0, 0, 0, 0, 384] := by
  decide +kernel

theorem primitive_host_0936_semantics :
    (Generated.hostChunk078[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[0]).mask = 262143 := by decide +kernel
  have hv : (Generated.hostChunk078[0]).primitive.toList = [36, 0, 0, 0, 0, 156, 552, 528, 0, 456, 72, 0, 0, 312, 0, 0, 0, 0, 0, 0, 0, 384] := by decide +kernel
  rw [hm, hv, primitive_values_0936]
  rfl

theorem primitive_values_0937 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375775) = [30, 0, 0, 0, 0, 120, 360, 360, 0, 360, 0, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 360] := by
  decide +kernel

theorem primitive_host_0937_semantics :
    (Generated.hostChunk078[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[1]).mask = 375775 := by decide +kernel
  have hv : (Generated.hostChunk078[1]).primitive.toList = [30, 0, 0, 0, 0, 120, 360, 360, 0, 360, 0, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 360] := by decide +kernel
  rw [hm, hv, primitive_values_0937]
  rfl

theorem primitive_values_0938 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375776) = [22, 0, 0, 0, 0, 60, 120, 120, 0, 120, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0938_semantics :
    (Generated.hostChunk078[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[2]).mask = 375776 := by decide +kernel
  have hv : (Generated.hostChunk078[2]).primitive.toList = [22, 0, 0, 0, 0, 60, 120, 120, 0, 120, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0938]
  rfl

theorem primitive_values_0939 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375777) = [24, 0, 0, 0, 0, 70, 156, 152, 0, 132, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by
  decide +kernel

theorem primitive_host_0939_semantics :
    (Generated.hostChunk078[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[3]).mask = 375777 := by decide +kernel
  have hv : (Generated.hostChunk078[3]).primitive.toList = [24, 0, 0, 0, 0, 70, 156, 152, 0, 132, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120] := by decide +kernel
  rw [hm, hv, primitive_values_0939]
  rfl

theorem primitive_values_0940 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375779) = [26, 0, 0, 0, 0, 82, 198, 196, 0, 158, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by
  decide +kernel

theorem primitive_host_0940_semantics :
    (Generated.hostChunk078[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[4]).mask = 375779 := by decide +kernel
  have hv : (Generated.hostChunk078[4]).primitive.toList = [26, 0, 0, 0, 0, 82, 198, 196, 0, 158, 12, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 132] := by decide +kernel
  rw [hm, hv, primitive_values_0940]
  rfl

theorem primitive_values_0941 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375783) = [28, 0, 0, 0, 0, 96, 252, 252, 0, 204, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by
  decide +kernel

theorem primitive_host_0941_semantics :
    (Generated.hostChunk078[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[5]).mask = 375783 := by decide +kernel
  have hv : (Generated.hostChunk078[5]).primitive.toList = [28, 0, 0, 0, 0, 96, 252, 252, 0, 204, 24, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 168] := by decide +kernel
  rw [hm, hv, primitive_values_0941]
  rfl

theorem primitive_values_0942 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375791) = [30, 0, 0, 0, 0, 112, 324, 320, 0, 276, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by
  decide +kernel

theorem primitive_host_0942_semantics :
    (Generated.hostChunk078[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[6]).mask = 375791 := by decide +kernel
  have hv : (Generated.hostChunk078[6]).primitive.toList = [30, 0, 0, 0, 0, 112, 324, 320, 0, 276, 24, 0, 0, 216, 0, 0, 0, 0, 0, 0, 0, 240] := by decide +kernel
  rw [hm, hv, primitive_values_0942]
  rfl

theorem primitive_values_0943 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375807) = [32, 0, 0, 0, 0, 130, 420, 400, 0, 380, 0, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 360] := by
  decide +kernel

theorem primitive_host_0943_semantics :
    (Generated.hostChunk078[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[7]).mask = 375807 := by decide +kernel
  have hv : (Generated.hostChunk078[7]).primitive.toList = [32, 0, 0, 0, 0, 130, 420, 400, 0, 380, 0, 0, 0, 360, 0, 0, 0, 0, 0, 0, 0, 360] := by decide +kernel
  rw [hm, hv, primitive_values_0943]
  rfl

theorem primitive_values_0944 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375841) = [18, 0, 0, 0, 0, 30, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0944_semantics :
    (Generated.hostChunk078[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[8]).mask = 375841 := by decide +kernel
  have hv : (Generated.hostChunk078[8]).primitive.toList = [18, 0, 0, 0, 0, 30, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0944]
  rfl

theorem primitive_values_0945 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375843) = [20, 0, 0, 0, 0, 40, 48, 52, 0, 32, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0945_semantics :
    (Generated.hostChunk078[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[9]).mask = 375843 := by decide +kernel
  have hv : (Generated.hostChunk078[9]).primitive.toList = [20, 0, 0, 0, 0, 40, 48, 52, 0, 32, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0945]
  rfl

theorem primitive_values_0946 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375847) = [22, 0, 0, 0, 0, 52, 84, 88, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0946_semantics :
    (Generated.hostChunk078[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[10]).mask = 375847 := by decide +kernel
  have hv : (Generated.hostChunk078[10]).primitive.toList = [22, 0, 0, 0, 0, 52, 84, 88, 0, 52, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0946]
  rfl

theorem primitive_values_0947 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 375855) = [24, 0, 0, 0, 0, 66, 138, 132, 0, 90, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by
  decide +kernel

theorem primitive_host_0947_semantics :
    (Generated.hostChunk078[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk078[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk078[11]).mask = 375855 := by decide +kernel
  have hv : (Generated.hostChunk078[11]).primitive.toList = [24, 0, 0, 0, 0, 66, 138, 132, 0, 90, 12, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 60] := by decide +kernel
  rw [hm, hv, primitive_values_0947]
  rfl

theorem primitive_chunk_078_semantics :
    ∀ h ∈ Generated.hostChunk078.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk078.toList = [Generated.hostChunk078[0], Generated.hostChunk078[1], Generated.hostChunk078[2], Generated.hostChunk078[3], Generated.hostChunk078[4], Generated.hostChunk078[5], Generated.hostChunk078[6], Generated.hostChunk078[7], Generated.hostChunk078[8], Generated.hostChunk078[9], Generated.hostChunk078[10], Generated.hostChunk078[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0936_semantics
  · exact primitive_host_0937_semantics
  · exact primitive_host_0938_semantics
  · exact primitive_host_0939_semantics
  · exact primitive_host_0940_semantics
  · exact primitive_host_0941_semantics
  · exact primitive_host_0942_semantics
  · exact primitive_host_0943_semantics
  · exact primitive_host_0944_semantics
  · exact primitive_host_0945_semantics
  · exact primitive_host_0946_semantics
  · exact primitive_host_0947_semantics

end InducedPentagons.Paper

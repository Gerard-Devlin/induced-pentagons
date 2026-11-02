import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData032
import InducedPentagonsPaper.Generated.PrimitiveRows024

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0384 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39479) = [18, 0, 0, 0, 0, 38, 72, 48, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0384_semantics :
    (Generated.hostChunk032[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[0]).mask = 39479 := by decide +kernel
  have hv : (Generated.hostChunk032[0]).primitive.toList = [18, 0, 0, 0, 0, 38, 72, 48, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0384]
  rfl

theorem primitive_values_0385 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39487) = [20, 0, 0, 0, 0, 52, 138, 76, 0, 50, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0385_semantics :
    (Generated.hostChunk032[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[1]).mask = 39487 := by decide +kernel
  have hv : (Generated.hostChunk032[1]).primitive.toList = [20, 0, 0, 0, 0, 52, 138, 76, 0, 50, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0385]
  rfl

theorem primitive_values_0386 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39509) = [16, 0, 0, 0, 0, 28, 24, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0386_semantics :
    (Generated.hostChunk032[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[2]).mask = 39509 := by decide +kernel
  have hv : (Generated.hostChunk032[2]).primitive.toList = [16, 0, 0, 0, 0, 28, 24, 36, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0386]
  rfl

theorem primitive_values_0387 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39511) = [18, 0, 0, 0, 0, 40, 60, 62, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem primitive_host_0387_semantics :
    (Generated.hostChunk032[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[3]).mask = 39511 := by decide +kernel
  have hv : (Generated.hostChunk032[3]).primitive.toList = [18, 0, 0, 0, 0, 40, 60, 62, 0, 32, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel
  rw [hm, hv, primitive_values_0387]
  rfl

theorem primitive_values_0388 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39516) = [16, 20, 12, 0, 0, 28, 24, 38, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0388_semantics :
    (Generated.hostChunk032[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[4]).mask = 39516 := by decide +kernel
  have hv : (Generated.hostChunk032[4]).primitive.toList = [16, 20, 12, 0, 0, 28, 24, 38, 0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0388]
  rfl

theorem primitive_values_0389 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39517) = [18, 0, 0, 0, 0, 38, 48, 60, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0389_semantics :
    (Generated.hostChunk032[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[5]).mask = 39517 := by decide +kernel
  have hv : (Generated.hostChunk032[5]).primitive.toList = [18, 0, 0, 0, 0, 38, 48, 60, 0, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0389]
  rfl

theorem primitive_values_0390 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39518) = [18, 0, 0, 0, 0, 40, 60, 64, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0390_semantics :
    (Generated.hostChunk032[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[6]).mask = 39518 := by decide +kernel
  have hv : (Generated.hostChunk032[6]).primitive.toList = [18, 0, 0, 0, 0, 40, 60, 64, 0, 36, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0390]
  rfl

theorem primitive_values_0391 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39519) = [20, 0, 0, 0, 0, 52, 102, 92, 0, 62, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by
  decide +kernel

theorem primitive_host_0391_semantics :
    (Generated.hostChunk032[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[7]).mask = 39519 := by decide +kernel
  have hv : (Generated.hostChunk032[7]).primitive.toList = [20, 0, 0, 0, 0, 52, 102, 92, 0, 62, 12, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 36] := by decide +kernel
  rw [hm, hv, primitive_values_0391]
  rfl

theorem primitive_values_0392 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39522) = [14, 0, 0, 0, 0, 20, 24, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0392_semantics :
    (Generated.hostChunk032[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[8]).mask = 39522 := by decide +kernel
  have hv : (Generated.hostChunk032[8]).primitive.toList = [14, 0, 0, 0, 0, 20, 24, 20, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0392]
  rfl

theorem primitive_values_0393 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39523) = [16, 0, 0, 0, 0, 28, 36, 34, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0393_semantics :
    (Generated.hostChunk032[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[9]).mask = 39523 := by decide +kernel
  have hv : (Generated.hostChunk032[9]).primitive.toList = [16, 0, 0, 0, 0, 28, 36, 34, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0393]
  rfl

theorem primitive_values_0394 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39524) = [14, 0, 0, 0, 0, 18, 12, 18, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0394_semantics :
    (Generated.hostChunk032[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[10]).mask = 39524 := by decide +kernel
  have hv : (Generated.hostChunk032[10]).primitive.toList = [14, 0, 0, 0, 0, 18, 12, 18, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0394]
  rfl

theorem primitive_values_0395 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 39525) = [16, 0, 0, 0, 0, 26, 24, 34, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0395_semantics :
    (Generated.hostChunk032[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk032[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk032[11]).mask = 39525 := by decide +kernel
  have hv : (Generated.hostChunk032[11]).primitive.toList = [16, 0, 0, 0, 0, 26, 24, 34, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0395]
  rfl

theorem primitive_chunk_032_semantics :
    ∀ h ∈ Generated.hostChunk032.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk032.toList = [Generated.hostChunk032[0], Generated.hostChunk032[1], Generated.hostChunk032[2], Generated.hostChunk032[3], Generated.hostChunk032[4], Generated.hostChunk032[5], Generated.hostChunk032[6], Generated.hostChunk032[7], Generated.hostChunk032[8], Generated.hostChunk032[9], Generated.hostChunk032[10], Generated.hostChunk032[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0384_semantics
  · exact primitive_host_0385_semantics
  · exact primitive_host_0386_semantics
  · exact primitive_host_0387_semantics
  · exact primitive_host_0388_semantics
  · exact primitive_host_0389_semantics
  · exact primitive_host_0390_semantics
  · exact primitive_host_0391_semantics
  · exact primitive_host_0392_semantics
  · exact primitive_host_0393_semantics
  · exact primitive_host_0394_semantics
  · exact primitive_host_0395_semantics

end InducedPentagons.Paper

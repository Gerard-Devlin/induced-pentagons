import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData045
import InducedPentagonsPaper.Generated.PrimitiveRows037

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_values_0540 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43878) = [18, 0, 0, 0, 0, 34, 42, 50, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0540_semantics :
    (Generated.hostChunk045[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[0]).mask = 43878 := by decide +kernel
  have hv : (Generated.hostChunk045[0]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 50, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0540]
  rfl

theorem primitive_values_0541 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43879) = [20, 0, 0, 0, 0, 46, 78, 82, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0541_semantics :
    (Generated.hostChunk045[1]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[1]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[1]).mask = 43879 := by decide +kernel
  have hv : (Generated.hostChunk045[1]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 82, 0, 30, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0541]
  rfl

theorem primitive_values_0542 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43884) = [18, 0, 0, 0, 0, 32, 30, 44, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0542_semantics :
    (Generated.hostChunk045[2]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[2]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[2]).mask = 43884 := by decide +kernel
  have hv : (Generated.hostChunk045[2]).primitive.toList = [18, 0, 0, 0, 0, 32, 30, 44, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0542]
  rfl

theorem primitive_values_0543 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43885) = [20, 0, 0, 0, 0, 44, 66, 74, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0543_semantics :
    (Generated.hostChunk045[3]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[3]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[3]).mask = 43885 := by decide +kernel
  have hv : (Generated.hostChunk045[3]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 74, 0, 24, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0543]
  rfl

theorem primitive_values_0544 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43887) = [22, 0, 0, 0, 0, 58, 120, 112, 0, 56, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem primitive_host_0544_semantics :
    (Generated.hostChunk045[4]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[4]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[4]).mask = 43887 := by decide +kernel
  have hv : (Generated.hostChunk045[4]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 112, 0, 56, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by decide +kernel
  rw [hm, hv, primitive_values_0544]
  rfl

theorem primitive_values_0545 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43888) = [16, 0, 0, 0, 0, 24, 18, 32, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0545_semantics :
    (Generated.hostChunk045[5]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[5]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[5]).mask = 43888 := by decide +kernel
  have hv : (Generated.hostChunk045[5]).primitive.toList = [16, 0, 0, 0, 0, 24, 18, 32, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0545]
  rfl

theorem primitive_values_0546 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43889) = [18, 0, 0, 0, 0, 34, 42, 52, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0546_semantics :
    (Generated.hostChunk045[6]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[6]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[6]).mask = 43889 := by decide +kernel
  have hv : (Generated.hostChunk045[6]).primitive.toList = [18, 0, 0, 0, 0, 34, 42, 52, 0, 16, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0546]
  rfl

theorem primitive_values_0547 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43891) = [20, 0, 0, 0, 0, 46, 78, 80, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by
  decide +kernel

theorem primitive_host_0547_semantics :
    (Generated.hostChunk045[7]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[7]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[7]).mask = 43891 := by decide +kernel
  have hv : (Generated.hostChunk045[7]).primitive.toList = [20, 0, 0, 0, 0, 46, 78, 80, 0, 42, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24] := by decide +kernel
  rw [hm, hv, primitive_values_0547]
  rfl

theorem primitive_values_0548 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43892) = [18, 10, 8, 0, 0, 32, 30, 50, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_host_0548_semantics :
    (Generated.hostChunk045[8]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[8]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[8]).mask = 43892 := by decide +kernel
  have hv : (Generated.hostChunk045[8]).primitive.toList = [18, 10, 8, 0, 0, 32, 30, 50, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_values_0548]
  rfl

theorem primitive_values_0549 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43893) = [20, 0, 0, 0, 0, 44, 66, 80, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem primitive_host_0549_semantics :
    (Generated.hostChunk045[9]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[9]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[9]).mask = 43893 := by decide +kernel
  have hv : (Generated.hostChunk045[9]).primitive.toList = [20, 0, 0, 0, 0, 44, 66, 80, 0, 18, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4] := by decide +kernel
  rw [hm, hv, primitive_values_0549]
  rfl

theorem primitive_values_0550 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43894) = [20, 10, 10, 4, 0, 44, 66, 76, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem primitive_host_0550_semantics :
    (Generated.hostChunk045[10]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[10]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[10]).mask = 43894 := by decide +kernel
  have hv : (Generated.hostChunk045[10]).primitive.toList = [20, 10, 10, 4, 0, 44, 66, 76, 0, 28, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] := by decide +kernel
  rw [hm, hv, primitive_values_0550]
  rfl

theorem primitive_values_0551 :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 43895) = [22, 0, 0, 0, 0, 58, 120, 114, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem primitive_host_0551_semantics :
    (Generated.hostChunk045[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk045[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk045[11]).mask = 43895 := by decide +kernel
  have hv : (Generated.hostChunk045[11]).primitive.toList = [22, 0, 0, 0, 0, 58, 120, 114, 0, 60, 8, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 32] := by decide +kernel
  rw [hm, hv, primitive_values_0551]
  rfl

theorem primitive_chunk_045_semantics :
    ∀ h ∈ Generated.hostChunk045.toList, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  have hr : Generated.hostChunk045.toList = [Generated.hostChunk045[0], Generated.hostChunk045[1], Generated.hostChunk045[2], Generated.hostChunk045[3], Generated.hostChunk045[4], Generated.hostChunk045[5], Generated.hostChunk045[6], Generated.hostChunk045[7], Generated.hostChunk045[8], Generated.hostChunk045[9], Generated.hostChunk045[10], Generated.hostChunk045[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_host_0540_semantics
  · exact primitive_host_0541_semantics
  · exact primitive_host_0542_semantics
  · exact primitive_host_0543_semantics
  · exact primitive_host_0544_semantics
  · exact primitive_host_0545_semantics
  · exact primitive_host_0546_semantics
  · exact primitive_host_0547_semantics
  · exact primitive_host_0548_semantics
  · exact primitive_host_0549_semantics
  · exact primitive_host_0550_semantics
  · exact primitive_host_0551_semantics

end InducedPentagons.Paper

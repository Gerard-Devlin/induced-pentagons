import InducedPentagonsPaper.Generated.PrimitivePatterns
import InducedPentagons.Generated.HostData000
import InducedPentagons.Generated.HostData086

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem primitive_empty_count_values :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 0) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem primitive_empty_host_semantics :
    (Generated.hostChunk000[0]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk000[0]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk000[0]).mask = 0 := by decide +kernel
  have hv : (Generated.hostChunk000[0]).primitive.toList = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  rw [hm, hv, primitive_empty_count_values]
  rfl

theorem primitive_complete_count_values :
    fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 2097151) = [42, 0, 0, 0, 0, 210, 840, 840, 0, 840, 0, 0, 0, 840, 0, 0, 0, 0, 0, 0, 0, 840] := by
  decide +kernel

theorem primitive_complete_host_semantics :
    (Generated.hostChunk086[11]).primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 (Generated.hostChunk086[11]).mask) := by
  apply fastPrimitiveRowCheck_sound primitivePatternSpecs primitivePatternSpecs_ordered
  unfold fastPrimitiveRowCheck
  have hm : (Generated.hostChunk086[11]).mask = 2097151 := by decide +kernel
  have hv : (Generated.hostChunk086[11]).primitive.toList = [42, 0, 0, 0, 0, 210, 840, 840, 0, 840, 0, 0, 0, 840, 0, 0, 0, 0, 0, 0, 0, 840] := by decide +kernel
  rw [hm, hv, primitive_complete_count_values]
  rfl

theorem primitive_changed_count_rejected :
    fastPrimitiveRowCheck primitivePatternSpecs
      { Generated.hostChunk000[0] with primitive := #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] } = false := by
  unfold fastPrimitiveRowCheck
  change ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] == fastPrimitiveCounts primitivePatternSpecs (maskGraph 7 0)) = false
  rw [primitive_empty_count_values]
  rfl

end InducedPentagons.Paper

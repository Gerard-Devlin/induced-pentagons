import InducedPentagonsPaper.FlagProductSemantics
import InducedPentagonsPaper.JointFlagEnumeration
import InducedPentagons.Generated.HostData000

/-! First direct kernel recounts of actual nonzero flag-product entries.
Zero entries and the remaining hosts still require the complete tensor checker. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem flagProduct_empty_one_root_value :
    flagProductCount_one_root (maskGraph 7 0) 0 0 = 140 := by
  unfold flagProductCount_one_root
  rw [← enumeratedJointFlagPairCount_eq]
  decide +kernel

theorem flagProduct_empty_independent3_value :
    flagProductCount_independent3 (maskGraph 7 0) 0 0 = 1260 := by
  unfold flagProductCount_independent3
  rw [← enumeratedJointFlagPairCount_eq]
  decide +kernel

theorem flagProduct_empty_nonzero_entries :
    (Generated.hostChunk000[0]).tensor.toList.map (fun e => (e.block, e.i, e.j, e.count)) =
      [(0, 0, 0, flagProductCount_one_root (maskGraph 7 (Generated.hostChunk000[0]).mask) 0 0),
       (1, 0, 0, flagProductCount_independent3 (maskGraph 7 (Generated.hostChunk000[0]).mask) 0 0)] := by
  have hm : (Generated.hostChunk000[0]).mask = 0 := by decide +kernel
  rw [hm, flagProduct_empty_one_root_value, flagProduct_empty_independent3_value]
  decide +kernel

end InducedPentagons.Paper

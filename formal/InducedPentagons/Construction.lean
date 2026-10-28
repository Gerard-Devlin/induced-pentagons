import InducedPentagons.Generated.ClebschData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace InducedPentagons
open Generated

/-- The complete normalized induced-cycle list is derived from graph adjacency. -/
theorem clebsch_pentagon_enumeration :
    inducedPentagons clebsch = clebschPentagonData := by decide +kernel

theorem clebsch_pentagons : (inducedPentagons clebsch).length = 192 := by
  rw [clebsch_pentagon_enumeration]
  decide +kernel

theorem clebsch_pentagons_nodup : (inducedPentagons clebsch).Nodup := by
  rw [clebsch_pentagon_enumeration]
  decide +kernel

/-- Squared sharp normalization on the explicitly counted equality construction. -/
theorem clebsch_sharp_normalization :
    (inducedPentagons clebsch).length ^ 2 * 25000 = 9 * (edgeCount clebsch) ^ 5 := by
  rw [clebsch_pentagons, clebsch_edges]

end InducedPentagons

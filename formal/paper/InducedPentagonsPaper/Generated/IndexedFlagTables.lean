import InducedPentagonsPaper.Generated.IndexedFlag_one_root
import InducedPentagonsPaper.Generated.IndexedFlag_independent3
import InducedPentagonsPaper.Generated.IndexedFlag_edge_isolate
import InducedPentagonsPaper.Generated.IndexedFlag_path3
import InducedPentagonsPaper.Generated.IndexedFlag_triangle3

namespace InducedPentagons.Paper

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem indexedFlag_wrong_index_rejected :
    flagIndexLookupCheck 4 6 1 0 indexedFlagBasis_one_root
      (fun m => if m.val = 0 then { indexedFlagLookup_one_root m with index := 1 }
        else indexedFlagLookup_one_root m) = false := by
  decide +kernel

end InducedPentagons.Paper

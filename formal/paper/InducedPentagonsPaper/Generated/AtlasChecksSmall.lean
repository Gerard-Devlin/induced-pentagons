import InducedPentagonsPaper.Generated.AtlasRowsSmall

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace InducedPentagons.Paper

theorem atlasRows0_checked :
    (atlasRows0).all (atlasRowCheck 0 atlasMasks1) = true := by
  decide +kernel

theorem atlasRows1_checked :
    (atlasRows1).all (atlasRowCheck 1 atlasMasks2) = true := by
  decide +kernel

theorem atlasRows2_checked :
    (atlasRows2).all (atlasRowCheck 2 atlasMasks3) = true := by
  decide +kernel

theorem atlasRows3_checked :
    (atlasRows3).all (atlasRowCheck 3 atlasMasks4) = true := by
  decide +kernel

theorem atlasRows4_checked :
    (atlasRows4).all (atlasRowCheck 4 atlasMasks5) = true := by
  decide +kernel

end InducedPentagons.Paper

import InducedPentagonsPaper.AtlasCensusRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRow1032 : AtlasCensusRow := ⟨454655, 4, 1260⟩

theorem atlasCensusRow1032_checked : atlasCensusRowCheck atlasCensusRow1032 = true := by
  decide +kernel

def atlasCensusRow1033 : AtlasCensusRow := ⟨458685, 4, 1260⟩

theorem atlasCensusRow1033_checked : atlasCensusRowCheck atlasCensusRow1033 = true := by
  decide +kernel

def atlasCensusRow1034 : AtlasCensusRow := ⟨458687, 4, 1260⟩

theorem atlasCensusRow1034_checked : atlasCensusRowCheck atlasCensusRow1034 = true := by
  decide +kernel

def atlasCensusRow1035 : AtlasCensusRow := ⟨458751, 12, 420⟩

theorem atlasCensusRow1035_checked : atlasCensusRowCheck atlasCensusRow1035 = true := by
  decide +kernel

def atlasCensusRow1036 : AtlasCensusRow := ⟨522111, 8, 630⟩

theorem atlasCensusRow1036_checked : atlasCensusRowCheck atlasCensusRow1036 = true := by
  decide +kernel

def atlasCensusRow1037 : AtlasCensusRow := ⟨522238, 16, 315⟩

theorem atlasCensusRow1037_checked : atlasCensusRowCheck atlasCensusRow1037 = true := by
  decide +kernel

def atlasCensusRow1038 : AtlasCensusRow := ⟨522239, 8, 630⟩

theorem atlasCensusRow1038_checked : atlasCensusRowCheck atlasCensusRow1038 = true := by
  decide +kernel

def atlasCensusRow1039 : AtlasCensusRow := ⟨524287, 48, 105⟩

theorem atlasCensusRow1039_checked : atlasCensusRowCheck atlasCensusRow1039 = true := by
  decide +kernel

def atlasCensusRow1040 : AtlasCensusRow := ⟨1015743, 48, 105⟩

theorem atlasCensusRow1040_checked : atlasCensusRowCheck atlasCensusRow1040 = true := by
  decide +kernel

def atlasCensusRow1041 : AtlasCensusRow := ⟨1015807, 48, 105⟩

theorem atlasCensusRow1041_checked : atlasCensusRowCheck atlasCensusRow1041 = true := by
  decide +kernel

def atlasCensusRow1042 : AtlasCensusRow := ⟨1048575, 240, 21⟩

theorem atlasCensusRow1042_checked : atlasCensusRowCheck atlasCensusRow1042 = true := by
  decide +kernel

def atlasCensusRow1043 : AtlasCensusRow := ⟨2097151, 5040, 1⟩

theorem atlasCensusRow1043_checked : atlasCensusRowCheck atlasCensusRow1043 = true := by
  decide +kernel

def atlasCensusRows43 : List AtlasCensusRow := [atlasCensusRow1032, atlasCensusRow1033, atlasCensusRow1034, atlasCensusRow1035, atlasCensusRow1036, atlasCensusRow1037, atlasCensusRow1038, atlasCensusRow1039, atlasCensusRow1040, atlasCensusRow1041, atlasCensusRow1042, atlasCensusRow1043]

theorem atlasCensusRows43_checked :
    atlasCensusRows43.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows43, List.all_cons, List.all_nil,
    atlasCensusRow1032_checked, atlasCensusRow1033_checked, atlasCensusRow1034_checked, atlasCensusRow1035_checked, atlasCensusRow1036_checked, atlasCensusRow1037_checked, atlasCensusRow1038_checked, atlasCensusRow1039_checked, atlasCensusRow1040_checked, atlasCensusRow1041_checked, atlasCensusRow1042_checked, atlasCensusRow1043_checked, Bool.and_self]

end InducedPentagons.Paper

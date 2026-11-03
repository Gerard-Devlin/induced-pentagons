import InducedPentagonsPaper.AtlasCensusRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRow0024 : AtlasCensusRow := ⟨206, 4, 1260⟩

theorem atlasCensusRow0024_checked : atlasCensusRowCheck atlasCensusRow0024 = true := by
  decide +kernel

def atlasCensusRow0025 : AtlasCensusRow := ⟨207, 4, 1260⟩

theorem atlasCensusRow0025_checked : atlasCensusRowCheck atlasCensusRow0025 = true := by
  decide +kernel

def atlasCensusRow0026 : AtlasCensusRow := ⟨216, 8, 630⟩

theorem atlasCensusRow0026_checked : atlasCensusRowCheck atlasCensusRow0026 = true := by
  decide +kernel

def atlasCensusRow0027 : AtlasCensusRow := ⟨217, 8, 630⟩

theorem atlasCensusRow0027_checked : atlasCensusRowCheck atlasCensusRow0027 = true := by
  decide +kernel

def atlasCensusRow0028 : AtlasCensusRow := ⟨218, 2, 2520⟩

theorem atlasCensusRow0028_checked : atlasCensusRowCheck atlasCensusRow0028 = true := by
  decide +kernel

def atlasCensusRow0029 : AtlasCensusRow := ⟨219, 2, 2520⟩

theorem atlasCensusRow0029_checked : atlasCensusRowCheck atlasCensusRow0029 = true := by
  decide +kernel

def atlasCensusRow0030 : AtlasCensusRow := ⟨222, 4, 1260⟩

theorem atlasCensusRow0030_checked : atlasCensusRowCheck atlasCensusRow0030 = true := by
  decide +kernel

def atlasCensusRow0031 : AtlasCensusRow := ⟨223, 4, 1260⟩

theorem atlasCensusRow0031_checked : atlasCensusRowCheck atlasCensusRow0031 = true := by
  decide +kernel

def atlasCensusRow0032 : AtlasCensusRow := ⟨248, 12, 420⟩

theorem atlasCensusRow0032_checked : atlasCensusRowCheck atlasCensusRow0032 = true := by
  decide +kernel

def atlasCensusRow0033 : AtlasCensusRow := ⟨249, 12, 420⟩

theorem atlasCensusRow0033_checked : atlasCensusRowCheck atlasCensusRow0033 = true := by
  decide +kernel

def atlasCensusRow0034 : AtlasCensusRow := ⟨250, 6, 840⟩

theorem atlasCensusRow0034_checked : atlasCensusRowCheck atlasCensusRow0034 = true := by
  decide +kernel

def atlasCensusRow0035 : AtlasCensusRow := ⟨251, 6, 840⟩

theorem atlasCensusRow0035_checked : atlasCensusRowCheck atlasCensusRow0035 = true := by
  decide +kernel

def atlasCensusRow0036 : AtlasCensusRow := ⟨254, 12, 420⟩

theorem atlasCensusRow0036_checked : atlasCensusRowCheck atlasCensusRow0036 = true := by
  decide +kernel

def atlasCensusRow0037 : AtlasCensusRow := ⟨255, 12, 420⟩

theorem atlasCensusRow0037_checked : atlasCensusRowCheck atlasCensusRow0037 = true := by
  decide +kernel

def atlasCensusRow0038 : AtlasCensusRow := ⟨462, 24, 210⟩

theorem atlasCensusRow0038_checked : atlasCensusRowCheck atlasCensusRow0038 = true := by
  decide +kernel

def atlasCensusRow0039 : AtlasCensusRow := ⟨463, 24, 210⟩

theorem atlasCensusRow0039_checked : atlasCensusRowCheck atlasCensusRow0039 = true := by
  decide +kernel

def atlasCensusRow0040 : AtlasCensusRow := ⟨470, 4, 1260⟩

theorem atlasCensusRow0040_checked : atlasCensusRowCheck atlasCensusRow0040 = true := by
  decide +kernel

def atlasCensusRow0041 : AtlasCensusRow := ⟨471, 4, 1260⟩

theorem atlasCensusRow0041_checked : atlasCensusRowCheck atlasCensusRow0041 = true := by
  decide +kernel

def atlasCensusRow0042 : AtlasCensusRow := ⟨478, 6, 840⟩

theorem atlasCensusRow0042_checked : atlasCensusRowCheck atlasCensusRow0042 = true := by
  decide +kernel

def atlasCensusRow0043 : AtlasCensusRow := ⟨479, 6, 840⟩

theorem atlasCensusRow0043_checked : atlasCensusRowCheck atlasCensusRow0043 = true := by
  decide +kernel

def atlasCensusRow0044 : AtlasCensusRow := ⟨498, 8, 630⟩

theorem atlasCensusRow0044_checked : atlasCensusRowCheck atlasCensusRow0044 = true := by
  decide +kernel

def atlasCensusRow0045 : AtlasCensusRow := ⟨499, 8, 630⟩

theorem atlasCensusRow0045_checked : atlasCensusRowCheck atlasCensusRow0045 = true := by
  decide +kernel

def atlasCensusRow0046 : AtlasCensusRow := ⟨502, 4, 1260⟩

theorem atlasCensusRow0046_checked : atlasCensusRowCheck atlasCensusRow0046 = true := by
  decide +kernel

def atlasCensusRow0047 : AtlasCensusRow := ⟨503, 4, 1260⟩

theorem atlasCensusRow0047_checked : atlasCensusRowCheck atlasCensusRow0047 = true := by
  decide +kernel

def atlasCensusRows01 : List AtlasCensusRow := [atlasCensusRow0024, atlasCensusRow0025, atlasCensusRow0026, atlasCensusRow0027, atlasCensusRow0028, atlasCensusRow0029, atlasCensusRow0030, atlasCensusRow0031, atlasCensusRow0032, atlasCensusRow0033, atlasCensusRow0034, atlasCensusRow0035, atlasCensusRow0036, atlasCensusRow0037, atlasCensusRow0038, atlasCensusRow0039, atlasCensusRow0040, atlasCensusRow0041, atlasCensusRow0042, atlasCensusRow0043, atlasCensusRow0044, atlasCensusRow0045, atlasCensusRow0046, atlasCensusRow0047]

theorem atlasCensusRows01_checked :
    atlasCensusRows01.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows01, List.all_cons, List.all_nil,
    atlasCensusRow0024_checked, atlasCensusRow0025_checked, atlasCensusRow0026_checked, atlasCensusRow0027_checked, atlasCensusRow0028_checked, atlasCensusRow0029_checked, atlasCensusRow0030_checked, atlasCensusRow0031_checked, atlasCensusRow0032_checked, atlasCensusRow0033_checked, atlasCensusRow0034_checked, atlasCensusRow0035_checked, atlasCensusRow0036_checked, atlasCensusRow0037_checked, atlasCensusRow0038_checked, atlasCensusRow0039_checked, atlasCensusRow0040_checked, atlasCensusRow0041_checked, atlasCensusRow0042_checked, atlasCensusRow0043_checked, atlasCensusRow0044_checked, atlasCensusRow0045_checked, atlasCensusRow0046_checked, atlasCensusRow0047_checked, Bool.and_self]

end InducedPentagons.Paper

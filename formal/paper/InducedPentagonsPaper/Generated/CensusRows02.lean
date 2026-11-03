import InducedPentagonsPaper.AtlasCensusRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRow0048 : AtlasCensusRow := ⟨510, 12, 420⟩

theorem atlasCensusRow0048_checked : atlasCensusRowCheck atlasCensusRow0048 = true := by
  decide +kernel

def atlasCensusRow0049 : AtlasCensusRow := ⟨511, 12, 420⟩

theorem atlasCensusRow0049_checked : atlasCensusRowCheck atlasCensusRow0049 = true := by
  decide +kernel

def atlasCensusRow0050 : AtlasCensusRow := ⟨990, 48, 105⟩

theorem atlasCensusRow0050_checked : atlasCensusRowCheck atlasCensusRow0050 = true := by
  decide +kernel

def atlasCensusRow0051 : AtlasCensusRow := ⟨991, 48, 105⟩

theorem atlasCensusRow0051_checked : atlasCensusRowCheck atlasCensusRow0051 = true := by
  decide +kernel

def atlasCensusRow0052 : AtlasCensusRow := ⟨1006, 12, 420⟩

theorem atlasCensusRow0052_checked : atlasCensusRowCheck atlasCensusRow0052 = true := by
  decide +kernel

def atlasCensusRow0053 : AtlasCensusRow := ⟨1007, 12, 420⟩

theorem atlasCensusRow0053_checked : atlasCensusRowCheck atlasCensusRow0053 = true := by
  decide +kernel

def atlasCensusRow0054 : AtlasCensusRow := ⟨1022, 24, 210⟩

theorem atlasCensusRow0054_checked : atlasCensusRowCheck atlasCensusRow0054 = true := by
  decide +kernel

def atlasCensusRow0055 : AtlasCensusRow := ⟨1023, 24, 210⟩

theorem atlasCensusRow0055_checked : atlasCensusRowCheck atlasCensusRow0055 = true := by
  decide +kernel

def atlasCensusRow0056 : AtlasCensusRow := ⟨2046, 240, 21⟩

theorem atlasCensusRow0056_checked : atlasCensusRowCheck atlasCensusRow0056 = true := by
  decide +kernel

def atlasCensusRow0057 : AtlasCensusRow := ⟨2047, 240, 21⟩

theorem atlasCensusRow0057_checked : atlasCensusRowCheck atlasCensusRow0057 = true := by
  decide +kernel

def atlasCensusRow0058 : AtlasCensusRow := ⟨2247, 144, 35⟩

theorem atlasCensusRow0058_checked : atlasCensusRowCheck atlasCensusRow0058 = true := by
  decide +kernel

def atlasCensusRow0059 : AtlasCensusRow := ⟨2248, 24, 210⟩

theorem atlasCensusRow0059_checked : atlasCensusRowCheck atlasCensusRow0059 = true := by
  decide +kernel

def atlasCensusRow0060 : AtlasCensusRow := ⟨2249, 4, 1260⟩

theorem atlasCensusRow0060_checked : atlasCensusRowCheck atlasCensusRow0060 = true := by
  decide +kernel

def atlasCensusRow0061 : AtlasCensusRow := ⟨2251, 4, 1260⟩

theorem atlasCensusRow0061_checked : atlasCensusRowCheck atlasCensusRow0061 = true := by
  decide +kernel

def atlasCensusRow0062 : AtlasCensusRow := ⟨2255, 12, 420⟩

theorem atlasCensusRow0062_checked : atlasCensusRowCheck atlasCensusRow0062 = true := by
  decide +kernel

def atlasCensusRow0063 : AtlasCensusRow := ⟨2264, 12, 420⟩

theorem atlasCensusRow0063_checked : atlasCensusRowCheck atlasCensusRow0063 = true := by
  decide +kernel

def atlasCensusRow0064 : AtlasCensusRow := ⟨2265, 4, 1260⟩

theorem atlasCensusRow0064_checked : atlasCensusRowCheck atlasCensusRow0064 = true := by
  decide +kernel

def atlasCensusRow0065 : AtlasCensusRow := ⟨2267, 4, 1260⟩

theorem atlasCensusRow0065_checked : atlasCensusRowCheck atlasCensusRow0065 = true := by
  decide +kernel

def atlasCensusRow0066 : AtlasCensusRow := ⟨2271, 12, 420⟩

theorem atlasCensusRow0066_checked : atlasCensusRowCheck atlasCensusRow0066 = true := by
  decide +kernel

def atlasCensusRow0067 : AtlasCensusRow := ⟨2296, 36, 140⟩

theorem atlasCensusRow0067_checked : atlasCensusRowCheck atlasCensusRow0067 = true := by
  decide +kernel

def atlasCensusRow0068 : AtlasCensusRow := ⟨2297, 12, 420⟩

theorem atlasCensusRow0068_checked : atlasCensusRowCheck atlasCensusRow0068 = true := by
  decide +kernel

def atlasCensusRow0069 : AtlasCensusRow := ⟨2299, 12, 420⟩

theorem atlasCensusRow0069_checked : atlasCensusRowCheck atlasCensusRow0069 = true := by
  decide +kernel

def atlasCensusRow0070 : AtlasCensusRow := ⟨2303, 36, 140⟩

theorem atlasCensusRow0070_checked : atlasCensusRowCheck atlasCensusRow0070 = true := by
  decide +kernel

def atlasCensusRow0071 : AtlasCensusRow := ⟨2319, 16, 315⟩

theorem atlasCensusRow0071_checked : atlasCensusRowCheck atlasCensusRow0071 = true := by
  decide +kernel

def atlasCensusRows02 : List AtlasCensusRow := [atlasCensusRow0048, atlasCensusRow0049, atlasCensusRow0050, atlasCensusRow0051, atlasCensusRow0052, atlasCensusRow0053, atlasCensusRow0054, atlasCensusRow0055, atlasCensusRow0056, atlasCensusRow0057, atlasCensusRow0058, atlasCensusRow0059, atlasCensusRow0060, atlasCensusRow0061, atlasCensusRow0062, atlasCensusRow0063, atlasCensusRow0064, atlasCensusRow0065, atlasCensusRow0066, atlasCensusRow0067, atlasCensusRow0068, atlasCensusRow0069, atlasCensusRow0070, atlasCensusRow0071]

theorem atlasCensusRows02_checked :
    atlasCensusRows02.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows02, List.all_cons, List.all_nil,
    atlasCensusRow0048_checked, atlasCensusRow0049_checked, atlasCensusRow0050_checked, atlasCensusRow0051_checked, atlasCensusRow0052_checked, atlasCensusRow0053_checked, atlasCensusRow0054_checked, atlasCensusRow0055_checked, atlasCensusRow0056_checked, atlasCensusRow0057_checked, atlasCensusRow0058_checked, atlasCensusRow0059_checked, atlasCensusRow0060_checked, atlasCensusRow0061_checked, atlasCensusRow0062_checked, atlasCensusRow0063_checked, atlasCensusRow0064_checked, atlasCensusRow0065_checked, atlasCensusRow0066_checked, atlasCensusRow0067_checked, atlasCensusRow0068_checked, atlasCensusRow0069_checked, atlasCensusRow0070_checked, atlasCensusRow0071_checked, Bool.and_self]

end InducedPentagons.Paper

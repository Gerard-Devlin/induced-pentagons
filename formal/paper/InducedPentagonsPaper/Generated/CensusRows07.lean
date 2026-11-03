import InducedPentagonsPaper.AtlasCensusRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRow0168 : AtlasCensusRow := ⟨3055, 4, 1260⟩

theorem atlasCensusRow0168_checked : atlasCensusRowCheck atlasCensusRow0168 = true := by
  decide +kernel

def atlasCensusRow0169 : AtlasCensusRow := ⟨3064, 4, 1260⟩

theorem atlasCensusRow0169_checked : atlasCensusRowCheck atlasCensusRow0169 = true := by
  decide +kernel

def atlasCensusRow0170 : AtlasCensusRow := ⟨3065, 4, 1260⟩

theorem atlasCensusRow0170_checked : atlasCensusRowCheck atlasCensusRow0170 = true := by
  decide +kernel

def atlasCensusRow0171 : AtlasCensusRow := ⟨3066, 2, 2520⟩

theorem atlasCensusRow0171_checked : atlasCensusRowCheck atlasCensusRow0171 = true := by
  decide +kernel

def atlasCensusRow0172 : AtlasCensusRow := ⟨3067, 2, 2520⟩

theorem atlasCensusRow0172_checked : atlasCensusRowCheck atlasCensusRow0172 = true := by
  decide +kernel

def atlasCensusRow0173 : AtlasCensusRow := ⟨3070, 4, 1260⟩

theorem atlasCensusRow0173_checked : atlasCensusRowCheck atlasCensusRow0173 = true := by
  decide +kernel

def atlasCensusRow0174 : AtlasCensusRow := ⟨3071, 4, 1260⟩

theorem atlasCensusRow0174_checked : atlasCensusRowCheck atlasCensusRow0174 = true := by
  decide +kernel

def atlasCensusRow0175 : AtlasCensusRow := ⟨3896, 24, 210⟩

theorem atlasCensusRow0175_checked : atlasCensusRowCheck atlasCensusRow0175 = true := by
  decide +kernel

def atlasCensusRow0176 : AtlasCensusRow := ⟨3897, 24, 210⟩

theorem atlasCensusRow0176_checked : atlasCensusRowCheck atlasCensusRow0176 = true := by
  decide +kernel

def atlasCensusRow0177 : AtlasCensusRow := ⟨3898, 6, 840⟩

theorem atlasCensusRow0177_checked : atlasCensusRowCheck atlasCensusRow0177 = true := by
  decide +kernel

def atlasCensusRow0178 : AtlasCensusRow := ⟨3899, 6, 840⟩

theorem atlasCensusRow0178_checked : atlasCensusRowCheck atlasCensusRow0178 = true := by
  decide +kernel

def atlasCensusRow0179 : AtlasCensusRow := ⟨3902, 12, 420⟩

theorem atlasCensusRow0179_checked : atlasCensusRowCheck atlasCensusRow0179 = true := by
  decide +kernel

def atlasCensusRow0180 : AtlasCensusRow := ⟨3903, 12, 420⟩

theorem atlasCensusRow0180_checked : atlasCensusRowCheck atlasCensusRow0180 = true := by
  decide +kernel

def atlasCensusRow0181 : AtlasCensusRow := ⟨3962, 12, 420⟩

theorem atlasCensusRow0181_checked : atlasCensusRowCheck atlasCensusRow0181 = true := by
  decide +kernel

def atlasCensusRow0182 : AtlasCensusRow := ⟨3963, 12, 420⟩

theorem atlasCensusRow0182_checked : atlasCensusRowCheck atlasCensusRow0182 = true := by
  decide +kernel

def atlasCensusRow0183 : AtlasCensusRow := ⟨3964, 12, 420⟩

theorem atlasCensusRow0183_checked : atlasCensusRowCheck atlasCensusRow0183 = true := by
  decide +kernel

def atlasCensusRow0184 : AtlasCensusRow := ⟨3965, 12, 420⟩

theorem atlasCensusRow0184_checked : atlasCensusRowCheck atlasCensusRow0184 = true := by
  decide +kernel

def atlasCensusRow0185 : AtlasCensusRow := ⟨3966, 6, 840⟩

theorem atlasCensusRow0185_checked : atlasCensusRowCheck atlasCensusRow0185 = true := by
  decide +kernel

def atlasCensusRow0186 : AtlasCensusRow := ⟨3967, 6, 840⟩

theorem atlasCensusRow0186_checked : atlasCensusRowCheck atlasCensusRow0186 = true := by
  decide +kernel

def atlasCensusRow0187 : AtlasCensusRow := ⟨4094, 24, 210⟩

theorem atlasCensusRow0187_checked : atlasCensusRowCheck atlasCensusRow0187 = true := by
  decide +kernel

def atlasCensusRow0188 : AtlasCensusRow := ⟨4095, 24, 210⟩

theorem atlasCensusRow0188_checked : atlasCensusRowCheck atlasCensusRow0188 = true := by
  decide +kernel

def atlasCensusRow0189 : AtlasCensusRow := ⟨6543, 16, 315⟩

theorem atlasCensusRow0189_checked : atlasCensusRowCheck atlasCensusRow0189 = true := by
  decide +kernel

def atlasCensusRow0190 : AtlasCensusRow := ⟨6549, 2, 2520⟩

theorem atlasCensusRow0190_checked : atlasCensusRowCheck atlasCensusRow0190 = true := by
  decide +kernel

def atlasCensusRow0191 : AtlasCensusRow := ⟨6551, 2, 2520⟩

theorem atlasCensusRow0191_checked : atlasCensusRowCheck atlasCensusRow0191 = true := by
  decide +kernel

def atlasCensusRows07 : List AtlasCensusRow := [atlasCensusRow0168, atlasCensusRow0169, atlasCensusRow0170, atlasCensusRow0171, atlasCensusRow0172, atlasCensusRow0173, atlasCensusRow0174, atlasCensusRow0175, atlasCensusRow0176, atlasCensusRow0177, atlasCensusRow0178, atlasCensusRow0179, atlasCensusRow0180, atlasCensusRow0181, atlasCensusRow0182, atlasCensusRow0183, atlasCensusRow0184, atlasCensusRow0185, atlasCensusRow0186, atlasCensusRow0187, atlasCensusRow0188, atlasCensusRow0189, atlasCensusRow0190, atlasCensusRow0191]

theorem atlasCensusRows07_checked :
    atlasCensusRows07.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows07, List.all_cons, List.all_nil,
    atlasCensusRow0168_checked, atlasCensusRow0169_checked, atlasCensusRow0170_checked, atlasCensusRow0171_checked, atlasCensusRow0172_checked, atlasCensusRow0173_checked, atlasCensusRow0174_checked, atlasCensusRow0175_checked, atlasCensusRow0176_checked, atlasCensusRow0177_checked, atlasCensusRow0178_checked, atlasCensusRow0179_checked, atlasCensusRow0180_checked, atlasCensusRow0181_checked, atlasCensusRow0182_checked, atlasCensusRow0183_checked, atlasCensusRow0184_checked, atlasCensusRow0185_checked, atlasCensusRow0186_checked, atlasCensusRow0187_checked, atlasCensusRow0188_checked, atlasCensusRow0189_checked, atlasCensusRow0190_checked, atlasCensusRow0191_checked, Bool.and_self]

end InducedPentagons.Paper

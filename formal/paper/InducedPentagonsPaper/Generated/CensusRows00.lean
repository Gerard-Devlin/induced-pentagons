import InducedPentagonsPaper.AtlasCensusRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRow0000 : AtlasCensusRow := ⟨0, 5040, 1⟩

theorem atlasCensusRow0000_checked : atlasCensusRowCheck atlasCensusRow0000 = true := by
  decide +kernel

def atlasCensusRow0001 : AtlasCensusRow := ⟨1, 240, 21⟩

theorem atlasCensusRow0001_checked : atlasCensusRowCheck atlasCensusRow0001 = true := by
  decide +kernel

def atlasCensusRow0002 : AtlasCensusRow := ⟨3, 48, 105⟩

theorem atlasCensusRow0002_checked : atlasCensusRowCheck atlasCensusRow0002 = true := by
  decide +kernel

def atlasCensusRow0003 : AtlasCensusRow := ⟨7, 36, 140⟩

theorem atlasCensusRow0003_checked : atlasCensusRowCheck atlasCensusRow0003 = true := by
  decide +kernel

def atlasCensusRow0004 : AtlasCensusRow := ⟨15, 48, 105⟩

theorem atlasCensusRow0004_checked : atlasCensusRowCheck atlasCensusRow0004 = true := by
  decide +kernel

def atlasCensusRow0005 : AtlasCensusRow := ⟨31, 120, 42⟩

theorem atlasCensusRow0005_checked : atlasCensusRowCheck atlasCensusRow0005 = true := by
  decide +kernel

def atlasCensusRow0006 : AtlasCensusRow := ⟨63, 720, 7⟩

theorem atlasCensusRow0006_checked : atlasCensusRowCheck atlasCensusRow0006 = true := by
  decide +kernel

def atlasCensusRow0007 : AtlasCensusRow := ⟨67, 144, 35⟩

theorem atlasCensusRow0007_checked : atlasCensusRowCheck atlasCensusRow0007 = true := by
  decide +kernel

def atlasCensusRow0008 : AtlasCensusRow := ⟨68, 48, 105⟩

theorem atlasCensusRow0008_checked : atlasCensusRowCheck atlasCensusRow0008 = true := by
  decide +kernel

def atlasCensusRow0009 : AtlasCensusRow := ⟨69, 12, 420⟩

theorem atlasCensusRow0009_checked : atlasCensusRowCheck atlasCensusRow0009 = true := by
  decide +kernel

def atlasCensusRow0010 : AtlasCensusRow := ⟨71, 12, 420⟩

theorem atlasCensusRow0010_checked : atlasCensusRowCheck atlasCensusRow0010 = true := by
  decide +kernel

def atlasCensusRow0011 : AtlasCensusRow := ⟨76, 8, 630⟩

theorem atlasCensusRow0011_checked : atlasCensusRowCheck atlasCensusRow0011 = true := by
  decide +kernel

def atlasCensusRow0012 : AtlasCensusRow := ⟨77, 4, 1260⟩

theorem atlasCensusRow0012_checked : atlasCensusRowCheck atlasCensusRow0012 = true := by
  decide +kernel

def atlasCensusRow0013 : AtlasCensusRow := ⟨79, 8, 630⟩

theorem atlasCensusRow0013_checked : atlasCensusRowCheck atlasCensusRow0013 = true := by
  decide +kernel

def atlasCensusRow0014 : AtlasCensusRow := ⟨92, 12, 420⟩

theorem atlasCensusRow0014_checked : atlasCensusRowCheck atlasCensusRow0014 = true := by
  decide +kernel

def atlasCensusRow0015 : AtlasCensusRow := ⟨93, 6, 840⟩

theorem atlasCensusRow0015_checked : atlasCensusRowCheck atlasCensusRow0015 = true := by
  decide +kernel

def atlasCensusRow0016 : AtlasCensusRow := ⟨95, 12, 420⟩

theorem atlasCensusRow0016_checked : atlasCensusRowCheck atlasCensusRow0016 = true := by
  decide +kernel

def atlasCensusRow0017 : AtlasCensusRow := ⟨124, 48, 105⟩

theorem atlasCensusRow0017_checked : atlasCensusRowCheck atlasCensusRow0017 = true := by
  decide +kernel

def atlasCensusRow0018 : AtlasCensusRow := ⟨125, 24, 210⟩

theorem atlasCensusRow0018_checked : atlasCensusRowCheck atlasCensusRow0018 = true := by
  decide +kernel

def atlasCensusRow0019 : AtlasCensusRow := ⟨127, 48, 105⟩

theorem atlasCensusRow0019_checked : atlasCensusRowCheck atlasCensusRow0019 = true := by
  decide +kernel

def atlasCensusRow0020 : AtlasCensusRow := ⟨198, 48, 105⟩

theorem atlasCensusRow0020_checked : atlasCensusRowCheck atlasCensusRow0020 = true := by
  decide +kernel

def atlasCensusRow0021 : AtlasCensusRow := ⟨199, 24, 210⟩

theorem atlasCensusRow0021_checked : atlasCensusRowCheck atlasCensusRow0021 = true := by
  decide +kernel

def atlasCensusRow0022 : AtlasCensusRow := ⟨202, 4, 1260⟩

theorem atlasCensusRow0022_checked : atlasCensusRowCheck atlasCensusRow0022 = true := by
  decide +kernel

def atlasCensusRow0023 : AtlasCensusRow := ⟨203, 4, 1260⟩

theorem atlasCensusRow0023_checked : atlasCensusRowCheck atlasCensusRow0023 = true := by
  decide +kernel

def atlasCensusRows00 : List AtlasCensusRow := [atlasCensusRow0000, atlasCensusRow0001, atlasCensusRow0002, atlasCensusRow0003, atlasCensusRow0004, atlasCensusRow0005, atlasCensusRow0006, atlasCensusRow0007, atlasCensusRow0008, atlasCensusRow0009, atlasCensusRow0010, atlasCensusRow0011, atlasCensusRow0012, atlasCensusRow0013, atlasCensusRow0014, atlasCensusRow0015, atlasCensusRow0016, atlasCensusRow0017, atlasCensusRow0018, atlasCensusRow0019, atlasCensusRow0020, atlasCensusRow0021, atlasCensusRow0022, atlasCensusRow0023]

theorem atlasCensusRows00_checked :
    atlasCensusRows00.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows00, List.all_cons, List.all_nil,
    atlasCensusRow0000_checked, atlasCensusRow0001_checked, atlasCensusRow0002_checked, atlasCensusRow0003_checked, atlasCensusRow0004_checked, atlasCensusRow0005_checked, atlasCensusRow0006_checked, atlasCensusRow0007_checked, atlasCensusRow0008_checked, atlasCensusRow0009_checked, atlasCensusRow0010_checked, atlasCensusRow0011_checked, atlasCensusRow0012_checked, atlasCensusRow0013_checked, atlasCensusRow0014_checked, atlasCensusRow0015_checked, atlasCensusRow0016_checked, atlasCensusRow0017_checked, atlasCensusRow0018_checked, atlasCensusRow0019_checked, atlasCensusRow0020_checked, atlasCensusRow0021_checked, atlasCensusRow0022_checked, atlasCensusRow0023_checked, Bool.and_self]

end InducedPentagons.Paper

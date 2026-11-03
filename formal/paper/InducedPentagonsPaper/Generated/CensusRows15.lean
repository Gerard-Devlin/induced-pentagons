import InducedPentagonsPaper.AtlasCensusRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRow0360 : AtlasCensusRow := ⟨39376, 48, 105⟩

theorem atlasCensusRow0360_checked : atlasCensusRowCheck atlasCensusRow0360 = true := by
  decide +kernel

def atlasCensusRow0361 : AtlasCensusRow := ⟨39377, 6, 840⟩

theorem atlasCensusRow0361_checked : atlasCensusRowCheck atlasCensusRow0361 = true := by
  decide +kernel

def atlasCensusRow0362 : AtlasCensusRow := ⟨39379, 4, 1260⟩

theorem atlasCensusRow0362_checked : atlasCensusRowCheck atlasCensusRow0362 = true := by
  decide +kernel

def atlasCensusRow0363 : AtlasCensusRow := ⟨39383, 6, 840⟩

theorem atlasCensusRow0363_checked : atlasCensusRowCheck atlasCensusRow0363 = true := by
  decide +kernel

def atlasCensusRow0364 : AtlasCensusRow := ⟨39391, 24, 210⟩

theorem atlasCensusRow0364_checked : atlasCensusRowCheck atlasCensusRow0364 = true := by
  decide +kernel

def atlasCensusRow0365 : AtlasCensusRow := ⟨39408, 48, 105⟩

theorem atlasCensusRow0365_checked : atlasCensusRowCheck atlasCensusRow0365 = true := by
  decide +kernel

def atlasCensusRow0366 : AtlasCensusRow := ⟨39409, 12, 420⟩

theorem atlasCensusRow0366_checked : atlasCensusRowCheck atlasCensusRow0366 = true := by
  decide +kernel

def atlasCensusRow0367 : AtlasCensusRow := ⟨39411, 8, 630⟩

theorem atlasCensusRow0367_checked : atlasCensusRowCheck atlasCensusRow0367 = true := by
  decide +kernel

def atlasCensusRow0368 : AtlasCensusRow := ⟨39415, 12, 420⟩

theorem atlasCensusRow0368_checked : atlasCensusRowCheck atlasCensusRow0368 = true := by
  decide +kernel

def atlasCensusRow0369 : AtlasCensusRow := ⟨39423, 48, 105⟩

theorem atlasCensusRow0369_checked : atlasCensusRowCheck atlasCensusRow0369 = true := by
  decide +kernel

def atlasCensusRow0370 : AtlasCensusRow := ⟨39441, 72, 70⟩

theorem atlasCensusRow0370_checked : atlasCensusRowCheck atlasCensusRow0370 = true := by
  decide +kernel

def atlasCensusRow0371 : AtlasCensusRow := ⟨39443, 8, 630⟩

theorem atlasCensusRow0371_checked : atlasCensusRowCheck atlasCensusRow0371 = true := by
  decide +kernel

def atlasCensusRow0372 : AtlasCensusRow := ⟨39447, 4, 1260⟩

theorem atlasCensusRow0372_checked : atlasCensusRowCheck atlasCensusRow0372 = true := by
  decide +kernel

def atlasCensusRow0373 : AtlasCensusRow := ⟨39455, 12, 420⟩

theorem atlasCensusRow0373_checked : atlasCensusRowCheck atlasCensusRow0373 = true := by
  decide +kernel

def atlasCensusRow0374 : AtlasCensusRow := ⟨39456, 48, 105⟩

theorem atlasCensusRow0374_checked : atlasCensusRowCheck atlasCensusRow0374 = true := by
  decide +kernel

def atlasCensusRow0375 : AtlasCensusRow := ⟨39457, 12, 420⟩

theorem atlasCensusRow0375_checked : atlasCensusRowCheck atlasCensusRow0375 = true := by
  decide +kernel

def atlasCensusRow0376 : AtlasCensusRow := ⟨39458, 4, 1260⟩

theorem atlasCensusRow0376_checked : atlasCensusRowCheck atlasCensusRow0376 = true := by
  decide +kernel

def atlasCensusRow0377 : AtlasCensusRow := ⟨39459, 2, 2520⟩

theorem atlasCensusRow0377_checked : atlasCensusRowCheck atlasCensusRow0377 = true := by
  decide +kernel

def atlasCensusRow0378 : AtlasCensusRow := ⟨39462, 4, 1260⟩

theorem atlasCensusRow0378_checked : atlasCensusRowCheck atlasCensusRow0378 = true := by
  decide +kernel

def atlasCensusRow0379 : AtlasCensusRow := ⟨39463, 2, 2520⟩

theorem atlasCensusRow0379_checked : atlasCensusRowCheck atlasCensusRow0379 = true := by
  decide +kernel

def atlasCensusRow0380 : AtlasCensusRow := ⟨39470, 12, 420⟩

theorem atlasCensusRow0380_checked : atlasCensusRowCheck atlasCensusRow0380 = true := by
  decide +kernel

def atlasCensusRow0381 : AtlasCensusRow := ⟨39471, 6, 840⟩

theorem atlasCensusRow0381_checked : atlasCensusRowCheck atlasCensusRow0381 = true := by
  decide +kernel

def atlasCensusRow0382 : AtlasCensusRow := ⟨39473, 12, 420⟩

theorem atlasCensusRow0382_checked : atlasCensusRowCheck atlasCensusRow0382 = true := by
  decide +kernel

def atlasCensusRow0383 : AtlasCensusRow := ⟨39475, 4, 1260⟩

theorem atlasCensusRow0383_checked : atlasCensusRowCheck atlasCensusRow0383 = true := by
  decide +kernel

def atlasCensusRows15 : List AtlasCensusRow := [atlasCensusRow0360, atlasCensusRow0361, atlasCensusRow0362, atlasCensusRow0363, atlasCensusRow0364, atlasCensusRow0365, atlasCensusRow0366, atlasCensusRow0367, atlasCensusRow0368, atlasCensusRow0369, atlasCensusRow0370, atlasCensusRow0371, atlasCensusRow0372, atlasCensusRow0373, atlasCensusRow0374, atlasCensusRow0375, atlasCensusRow0376, atlasCensusRow0377, atlasCensusRow0378, atlasCensusRow0379, atlasCensusRow0380, atlasCensusRow0381, atlasCensusRow0382, atlasCensusRow0383]

theorem atlasCensusRows15_checked :
    atlasCensusRows15.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows15, List.all_cons, List.all_nil,
    atlasCensusRow0360_checked, atlasCensusRow0361_checked, atlasCensusRow0362_checked, atlasCensusRow0363_checked, atlasCensusRow0364_checked, atlasCensusRow0365_checked, atlasCensusRow0366_checked, atlasCensusRow0367_checked, atlasCensusRow0368_checked, atlasCensusRow0369_checked, atlasCensusRow0370_checked, atlasCensusRow0371_checked, atlasCensusRow0372_checked, atlasCensusRow0373_checked, atlasCensusRow0374_checked, atlasCensusRow0375_checked, atlasCensusRow0376_checked, atlasCensusRow0377_checked, atlasCensusRow0378_checked, atlasCensusRow0379_checked, atlasCensusRow0380_checked, atlasCensusRow0381_checked, atlasCensusRow0382_checked, atlasCensusRow0383_checked, Bool.and_self]

end InducedPentagons.Paper

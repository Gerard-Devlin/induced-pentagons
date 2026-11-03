import InducedPentagonsPaper.FlagTensorTrie
import InducedPentagons.Generated.HostData000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def tensorExampleData_empty : List (Nat × Nat) := [(0, 140), (5184, 1260)]

theorem tensor_empty_checked : fastTrieTensorCheck 0 tensorExampleData_empty = true := by
  decide +kernel

theorem tensor_empty_binding :
    (Generated.hostChunk000[0]).mask = 0 ∧ rawFlagTensorEntries (Generated.hostChunk000[0]) = tensorExampleData_empty := by
  decide +kernel

theorem tensor_empty_row_checked : fastTrieTensorRowCheck (Generated.hostChunk000[0]) = true := by
  unfold fastTrieTensorRowCheck
  rw [tensor_empty_binding.1, tensor_empty_binding.2]
  exact tensor_empty_checked

theorem tensor_empty_all_key_counts : ∀ k, k < 32768 →
    weightedCountAt (rawFlagTensorEntries (Generated.hostChunk000[0])) k =
      (flagTensorKeys (maskGraph 7 (Generated.hostChunk000[0]).mask)).count k :=
  fastTrieTensorRowCheck_sound (Generated.hostChunk000[0]) tensor_empty_row_checked

end InducedPentagons.Paper

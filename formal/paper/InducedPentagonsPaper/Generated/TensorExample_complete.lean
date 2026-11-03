import InducedPentagonsPaper.FlagTensorTrie
import InducedPentagons.Generated.HostData086

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def tensorExampleData_complete : List (Nat × Nat) := [(1387, 140), (25919, 1260)]

theorem tensor_complete_checked : fastTrieTensorCheck 2097151 tensorExampleData_complete = true := by
  decide +kernel

theorem tensor_complete_binding :
    (Generated.hostChunk086[11]).mask = 2097151 ∧ rawFlagTensorEntries (Generated.hostChunk086[11]) = tensorExampleData_complete := by
  decide +kernel

theorem tensor_complete_row_checked : fastTrieTensorRowCheck (Generated.hostChunk086[11]) = true := by
  unfold fastTrieTensorRowCheck
  rw [tensor_complete_binding.1, tensor_complete_binding.2]
  exact tensor_complete_checked

theorem tensor_complete_all_key_counts : ∀ k, k < 32768 →
    weightedCountAt (rawFlagTensorEntries (Generated.hostChunk086[11])) k =
      (flagTensorKeys (maskGraph 7 (Generated.hostChunk086[11]).mask)).count k :=
  fastTrieTensorRowCheck_sound (Generated.hostChunk086[11]) tensor_complete_row_checked

end InducedPentagons.Paper

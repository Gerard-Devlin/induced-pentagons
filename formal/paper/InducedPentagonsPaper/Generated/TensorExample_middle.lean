import InducedPentagonsPaper.FlagTensorTrie
import InducedPentagons.Generated.HostData043

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def tensorExampleData_middle : List (Nat × Nat) := [(78, 4), (88, 4), (90, 8), (159, 8), (222, 8), (294, 2), (297, 2), (305, 2), (306, 6), (307, 4), (371, 8), (373, 8), (441, 4), (443, 8), (447, 4), (520, 2), (522, 6), (587, 8), (591, 8), (593, 4), (595, 4), (661, 4), (732, 8), (877, 8), (880, 4), (881, 4), (5608, 4), (5613, 4), (5615, 8), (6093, 4), (6117, 4), (6119, 8), (6467, 8), (6474, 8), (6525, 4), (6544, 4), (6551, 8), (6893, 8), (6906, 8), (7397, 8), (7403, 8), (8264, 8), (8408, 8), (8767, 8), (8986, 8), (8993, 8), (9207, 8), (10857, 8), (11004, 8), (11041, 8), (11133, 4), (11152, 4), (11157, 4), (11159, 4), (11346, 8), (11349, 8), (11499, 8), (11922, 8), (11996, 8), (11997, 8), (12140, 8), (12213, 4), (12579, 8), (13024, 2), (13029, 2), (13031, 4), (13161, 4), (13304, 8), (13524, 4), (13799, 4), (13815, 8), (14018, 4), (14033, 8), (15738, 8), (15899, 8), (15971, 8), (15982, 8), (16143, 8), (16158, 8), (16619, 8), (16654, 8), (16763, 8), (16798, 8), (16819, 4), (16907, 8), (16909, 8), (17051, 8), (17489, 8), (17755, 4), (18330, 4), (18421, 8), (18430, 8), (20081, 4), (20861, 8), (20895, 8), (21011, 8), (21033, 8), (21049, 8), (21255, 8), (21399, 8), (21404, 8), (21522, 8), (21556, 8), (21560, 8), (21777, 8), (21778, 8), (21842, 8), (21844, 8), (21849, 8), (21921, 8), (21957, 4), (22132, 8), (22168, 4), (22221, 4), (22576, 8), (23087, 8), (23234, 8), (23453, 8), (23603, 8), (23661, 4), (24114, 8), (24184, 4), (24405, 4)]

theorem tensor_middle_checked : fastTrieTensorCheck 42479 tensorExampleData_middle = true := by
  decide +kernel

theorem tensor_middle_binding :
    (Generated.hostChunk043[6]).mask = 42479 ∧ rawFlagTensorEntries (Generated.hostChunk043[6]) = tensorExampleData_middle := by
  decide +kernel

theorem tensor_middle_row_checked : fastTrieTensorRowCheck (Generated.hostChunk043[6]) = true := by
  unfold fastTrieTensorRowCheck
  rw [tensor_middle_binding.1, tensor_middle_binding.2]
  exact tensor_middle_checked

theorem tensor_middle_all_key_counts : ∀ k, k < 32768 →
    weightedCountAt (rawFlagTensorEntries (Generated.hostChunk043[6])) k =
      (flagTensorKeys (maskGraph 7 (Generated.hostChunk043[6]).mask)).count k :=
  fastTrieTensorRowCheck_sound (Generated.hostChunk043[6]) tensor_middle_row_checked

end InducedPentagons.Paper

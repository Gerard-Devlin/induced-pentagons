import InducedPentagonsPaper.CountTrie
import InducedPentagonsPaper.FlagTensorMeaning

/-! A sparse histogram checker for complete flag-product tensor rows. -/

namespace InducedPentagons.Paper

def fastTrieTensorCheck (mask : Nat) (entries : List (Nat × Nat)) : Bool :=
  entries.all (fun e => decide (e.1 < 32768)) &&
    decide (CountTrie.ofWeighted 15 entries = CountTrie.ofKeys 15 (flagTensorKeys (maskGraph 7 mask)))

def fastTrieTensorRowCheck (h : HostRow) : Bool :=
  fastTrieTensorCheck h.mask (rawFlagTensorEntries h)

theorem fastTrieTensorRowCheck_sound (h : HostRow) (hc : fastTrieTensorRowCheck h = true) :
    ∀ k, k < 32768 → weightedCountAt (rawFlagTensorEntries h) k =
      (flagTensorKeys (maskGraph 7 h.mask)).count k := by
  simp only [fastTrieTensorRowCheck, fastTrieTensorCheck, Bool.and_eq_true_iff,
    List.all_eq_true, decide_eq_true_eq] at hc
  intro k hk
  have he := congrArg (CountTrie.lookup 15 k) hc.2
  rw [CountTrie.lookup_ofWeighted 15 _ hc.1 k hk,
    CountTrie.lookup_ofKeys 15 _ (flagTensorKeys_bounded _) k hk] at he
  exact he

end InducedPentagons.Paper

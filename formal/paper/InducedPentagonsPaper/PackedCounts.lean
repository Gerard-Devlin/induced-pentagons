import Mathlib.Tactic

/-! Exact histogram digits in a carry-free sum of powers. -/

namespace InducedPentagons.Paper

def countPowerCode (base : Nat) (keys : Multiset Nat) : Nat :=
  (keys.map (fun k => base ^ k)).sum

def shiftedCountKeys (keys : Multiset Nat) : Multiset Nat :=
  (keys.filter (fun k => k ≠ 0)).map Nat.pred

@[simp] theorem countPowerCode_zero (base : Nat) : countPowerCode base 0 = 0 := by
  simp [countPowerCode]

@[simp] theorem countPowerCode_cons (base a : Nat) (keys : Multiset Nat) :
    countPowerCode base (a ::ₘ keys) = base ^ a + countPowerCode base keys := by
  simp [countPowerCode]

@[simp] theorem shiftedCountKeys_zero : shiftedCountKeys 0 = 0 := by
  simp [shiftedCountKeys]

@[simp] theorem shiftedCountKeys_cons_zero (keys : Multiset Nat) :
    shiftedCountKeys (0 ::ₘ keys) = shiftedCountKeys keys := by
  simp [shiftedCountKeys]

@[simp] theorem shiftedCountKeys_cons_succ (a : Nat) (keys : Multiset Nat) :
    shiftedCountKeys ((a + 1) ::ₘ keys) = a ::ₘ shiftedCountKeys keys := by
  simp [shiftedCountKeys]

theorem shiftedCountKeys_card_le (keys : Multiset Nat) :
    (shiftedCountKeys keys).card ≤ keys.card := by
  simp only [shiftedCountKeys, Multiset.card_map]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem shiftedCountKeys_count (keys : Multiset Nat) (k : Nat) :
    (shiftedCountKeys keys).count k = keys.count (k + 1) := by
  induction keys using Multiset.induction_on with
  | empty => simp
  | @cons a keys ih =>
    cases a with
    | zero => simp [ih]
    | succ a => simp [Multiset.count_cons, ih]

theorem countPowerCode_split (base : Nat) (keys : Multiset Nat) :
    countPowerCode base keys = keys.count 0 + base * countPowerCode base (shiftedCountKeys keys) := by
  induction keys using Multiset.induction_on with
  | empty => simp
  | @cons a keys ih =>
    cases a with
    | zero => simp only [countPowerCode_cons, pow_zero, shiftedCountKeys_cons_zero,
        Multiset.count_cons_self, ih]; omega
    | succ a =>
      simp only [countPowerCode_cons, shiftedCountKeys_cons_succ, Nat.pow_succ',
        Multiset.count_cons_of_ne (Nat.zero_ne_add_one a), ih]
      ring

theorem countPowerCode_div_base {base : Nat} {keys : Multiset Nat}
    (hb : 0 < base) (hk : keys.card < base) :
    countPowerCode base keys / base = countPowerCode base (shiftedCountKeys keys) := by
  rw [countPowerCode_split, Nat.add_mul_div_left _ _ hb]
  have hz : keys.count 0 < base := lt_of_le_of_lt (Multiset.count_le_card _ _) hk
  rw [Nat.div_eq_of_lt hz, zero_add]

theorem countPowerCode_digit {base : Nat} (hb : 0 < base) (keys : Multiset Nat)
    (hk : keys.card < base) (k : Nat) :
    (countPowerCode base keys / base ^ k) % base = keys.count k := by
  induction k generalizing keys with
  | zero =>
    simp only [pow_zero, Nat.div_one]
    rw [countPowerCode_split, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Multiset.count_le_card _ _) hk)
  | succ k ih =>
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, countPowerCode_div_base hb hk]
    rw [ih (shiftedCountKeys keys) (lt_of_le_of_lt (shiftedCountKeys_card_le keys) hk),
      shiftedCountKeys_count]

def boundedPower (base : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, k =>
    if k = 0 then 1 else
      let v := boundedPower base fuel (k / 2)
      if k % 2 = 0 then v * v else base * v * v

theorem boundedPower_eq (base fuel k : Nat) (hk : k < 2 ^ fuel) :
    boundedPower base fuel k = base ^ k := by
  induction fuel generalizing k with
  | zero =>
    have he : k = 0 := by simpa using hk
    simp [boundedPower, he]
  | succ fuel ih =>
    by_cases hzero : k = 0
    · simp [boundedPower, hzero]
    have hq : k / 2 < 2 ^ fuel := by
      have hp : 0 < 2 := by decide
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [Nat.pow_succ] using hk
    simp only [boundedPower, if_neg hzero, ih (k / 2) hq]
    have hmod := Nat.mod_lt k (by decide : 0 < 2)
    have hsplit := Nat.mod_add_div k 2
    by_cases heven : k % 2 = 0
    · rw [if_pos heven]
      have he : k = k / 2 + k / 2 := by omega
      calc
        _ = base ^ (k / 2 + k / 2) := (Nat.pow_add _ _ _).symm
        _ = base ^ k := congrArg (fun e => base ^ e) he.symm
    · rw [if_neg heven]
      have he : k = k / 2 + k / 2 + 1 := by omega
      calc
        _ = base ^ (k / 2 + k / 2 + 1) := by rw [Nat.pow_succ, Nat.pow_add]; ring
        _ = base ^ k := congrArg (fun e => base ^ e) he.symm

def fastCountPowerCode (base fuel : Nat) (keys : Multiset Nat) : Nat :=
  (keys.map (boundedPower base fuel)).sum

theorem fastCountPowerCode_eq (base fuel : Nat) (keys : Multiset Nat)
    (hk : ∀ k ∈ keys, k < 2 ^ fuel) :
    fastCountPowerCode base fuel keys = countPowerCode base keys := by
  unfold fastCountPowerCode countPowerCode
  congr 1
  apply Multiset.map_congr rfl
  exact fun k hmem => boundedPower_eq base fuel k (hk k hmem)

theorem fastCountPowerCode_digit {base fuel : Nat} (hb : 0 < base) (keys : Multiset Nat)
    (hc : keys.card < base) (hk : ∀ k ∈ keys, k < 2 ^ fuel) (k : Nat) :
    (fastCountPowerCode base fuel keys / base ^ k) % base = keys.count k := by
  rw [fastCountPowerCode_eq base fuel keys hk]
  exact countPowerCode_digit hb keys hc k

def weightedCountKeys (entries : List (Nat × Nat)) : Multiset Nat :=
  entries.foldr (fun e rest => Multiset.replicate e.2 e.1 + rest) 0

def weightedCountAt (entries : List (Nat × Nat)) (k : Nat) : Nat :=
  (entries.map (fun e => if e.1 = k then e.2 else 0)).sum

def weightedCountCode (base fuel : Nat) (entries : List (Nat × Nat)) : Nat :=
  entries.foldr (fun e rest => e.2 * boundedPower base fuel e.1 + rest) 0

theorem weightedCountKeys_card (entries : List (Nat × Nat)) :
    (weightedCountKeys entries).card = (entries.map Prod.snd).sum := by
  induction entries with
  | nil => simp [weightedCountKeys]
  | cons e entries ih =>
    simpa only [weightedCountKeys, List.foldr_cons, Multiset.card_add,
      Multiset.card_replicate, List.map_cons, List.sum_cons, Nat.add_left_cancel_iff] using ih

theorem weightedCountKeys_count (entries : List (Nat × Nat)) (k : Nat) :
    (weightedCountKeys entries).count k = weightedCountAt entries k := by
  induction entries with
  | nil => simp [weightedCountKeys, weightedCountAt]
  | cons e entries ih =>
    simp only [weightedCountKeys, List.foldr_cons, Multiset.count_add]
    change (Multiset.replicate e.2 e.1).count k + (weightedCountKeys entries).count k = _
    rw [ih, Multiset.count_replicate]
    simp [weightedCountAt, eq_comm]

theorem weightedCountKeys_bounded (entries : List (Nat × Nat)) (bound : Nat)
    (hk : ∀ e ∈ entries, e.1 < bound) :
    ∀ k ∈ weightedCountKeys entries, k < bound := by
  induction entries with
  | nil => simp [weightedCountKeys]
  | cons e entries ih =>
    intro k hmem
    rcases Multiset.mem_add.mp hmem with he | ht
    · have heq : k = e.1 := (Multiset.mem_replicate.mp he).2
      rw [heq]
      exact hk e (by simp)
    · exact ih (fun q hq => hk q (by simp [hq])) k ht

theorem weightedCountCode_eq (base fuel : Nat) (entries : List (Nat × Nat)) :
    weightedCountCode base fuel entries = fastCountPowerCode base fuel (weightedCountKeys entries) := by
  induction entries with
  | nil => simp [weightedCountCode, fastCountPowerCode, weightedCountKeys]
  | cons e entries ih =>
    simp only [weightedCountCode, List.foldr_cons, weightedCountKeys,
      fastCountPowerCode, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Nat.nsmul_eq_mul] at ih ⊢
    rw [ih]

theorem weightedCountCode_digit {base fuel : Nat} (hb : 0 < base)
    (entries : List (Nat × Nat)) (hc : (entries.map Prod.snd).sum < base)
    (hk : ∀ e ∈ entries, e.1 < 2 ^ fuel) (k : Nat) :
    (weightedCountCode base fuel entries / base ^ k) % base = weightedCountAt entries k := by
  rw [weightedCountCode_eq, fastCountPowerCode_digit hb _
    (by rwa [weightedCountKeys_card]) (weightedCountKeys_bounded entries _ hk),
    weightedCountKeys_count]

theorem weightedCountCode_counts_of_eq {base fuel : Nat} (hb : 0 < base)
    (entries : List (Nat × Nat)) (keys : Multiset Nat)
    (hc : (entries.map Prod.snd).sum < base) (hkeys : keys.card < base)
    (he : ∀ e ∈ entries, e.1 < 2 ^ fuel) (hk : ∀ k ∈ keys, k < 2 ^ fuel)
    (hcode : weightedCountCode base fuel entries = fastCountPowerCode base fuel keys) :
    ∀ k, weightedCountAt entries k = keys.count k := by
  intro k
  rw [← weightedCountCode_digit hb entries hc he k,
    ← fastCountPowerCode_digit hb keys hkeys hk k, hcode]

end InducedPentagons.Paper

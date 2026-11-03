import Mathlib.Tactic

/-! Sparse binary histograms with bounded-key lookup semantics. -/

namespace InducedPentagons.Paper

inductive CountTrie where
  | empty
  | leaf (count : Nat)
  | branch (left right : CountTrie)
  deriving DecidableEq

namespace CountTrie

def left : CountTrie → CountTrie
  | branch l _ => l
  | _ => empty

def right : CountTrie → CountTrie
  | branch _ r => r
  | _ => empty

def value : CountTrie → Nat
  | leaf n => n
  | _ => 0

def lookup : Nat → Nat → CountTrie → Nat
  | 0, _, t => t.value
  | depth + 1, key, t =>
    if key % 2 = 0 then lookup depth (key / 2) t.left
    else lookup depth (key / 2) t.right

def add : Nat → Nat → Nat → CountTrie → CountTrie
  | 0, _, amount, t => leaf (t.value + amount)
  | depth + 1, key, amount, t =>
    if key % 2 = 0 then branch (add depth (key / 2) amount t.left) t.right
    else branch t.left (add depth (key / 2) amount t.right)

theorem lookup_empty (depth key : Nat) : lookup depth key empty = 0 := by
  induction depth generalizing key with
  | zero => rfl
  | succ depth ih => simp [lookup, left, right, ih]

theorem add_commute (depth key amount key' amount' : Nat) (t : CountTrie) :
    add depth key amount (add depth key' amount' t) =
      add depth key' amount' (add depth key amount t) := by
  induction depth generalizing key key' t with
  | zero => simp [add, value, Nat.add_comm, Nat.add_left_comm]
  | succ depth ih =>
    by_cases hk : key % 2 = 0 <;> by_cases hk' : key' % 2 = 0
    all_goals simp only [add, hk, hk', ite_true, ite_false, left, right]
    all_goals congr 1; apply ih

theorem lookup_add (depth query key amount : Nat) (t : CountTrie)
    (hq : query < 2 ^ depth) (hk : key < 2 ^ depth) :
    lookup depth query (add depth key amount t) =
      lookup depth query t + if query = key then amount else 0 := by
  induction depth generalizing query key t with
  | zero =>
    have hq0 : query = 0 := by simpa using hq
    have hk0 : key = 0 := by simpa using hk
    simp [hq0, hk0, add, lookup, value]
  | succ depth ih =>
    have hq' : query / 2 < 2 ^ depth := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
      simpa only [Nat.pow_succ] using hq
    have hk' : key / 2 < 2 ^ depth := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
      simpa only [Nat.pow_succ] using hk
    have hqr := Nat.mod_lt query (by decide : 0 < 2)
    have hkr := Nat.mod_lt key (by decide : 0 < 2)
    have hqd := Nat.mod_add_div query 2
    have hkd := Nat.mod_add_div key 2
    by_cases heq : query % 2 = 0 <;> by_cases hek : key % 2 = 0
    · have he : query / 2 = key / 2 ↔ query = key := by omega
      have ht := ih (query / 2) (key / 2) t.left hq' hk'
      simp only [he] at ht
      simpa only [lookup, add, heq, hek, ite_true, left] using ht
    · have he : query ≠ key := by omega
      simp [lookup, add, heq, hek, left, right, he]
    · have he : query ≠ key := by omega
      simp [lookup, add, heq, hek, left, right, he]
    · have he : query / 2 = key / 2 ↔ query = key := by omega
      have ht := ih (query / 2) (key / 2) t.right hq' hk'
      simp only [he] at ht
      simpa only [lookup, add, heq, hek, ite_false, right] using ht

instance (depth : Nat) : LeftCommutative (fun key t => add depth key 1 t) :=
  ⟨fun a b t => add_commute depth a 1 b 1 t⟩

def ofKeys (depth : Nat) (keys : Multiset Nat) : CountTrie :=
  keys.foldr (fun key t => add depth key 1 t) empty

theorem lookup_ofKeys (depth : Nat) (keys : Multiset Nat)
    (hk : ∀ k ∈ keys, k < 2 ^ depth) (query : Nat) (hq : query < 2 ^ depth) :
    lookup depth query (ofKeys depth keys) = keys.count query := by
  induction keys using Multiset.induction_on with
  | empty => simp [ofKeys, lookup_empty]
  | @cons k keys ih =>
    have ha := hk k (by simp)
    have hr : ∀ q ∈ keys, q < 2 ^ depth := fun q h => hk q (by simp [h])
    rw [ofKeys, Multiset.foldr_cons]
    change lookup depth query (add depth k 1 (ofKeys depth keys)) = _
    rw [lookup_add depth query k 1 _ hq ha, ih hr]
    simp [Multiset.count_cons, eq_comm]

def ofWeighted (depth : Nat) (entries : List (Nat × Nat)) : CountTrie :=
  entries.foldr (fun e t => add depth e.1 e.2 t) empty

theorem lookup_ofWeighted (depth : Nat) (entries : List (Nat × Nat))
    (hk : ∀ e ∈ entries, e.1 < 2 ^ depth) (query : Nat) (hq : query < 2 ^ depth) :
    lookup depth query (ofWeighted depth entries) =
      (entries.map (fun e => if e.1 = query then e.2 else 0)).sum := by
  induction entries with
  | nil => simp [ofWeighted, lookup_empty]
  | cons e entries ih =>
    have ha := hk e (by simp)
    have hr : ∀ q ∈ entries, q.1 < 2 ^ depth := fun q h => hk q (by simp [h])
    change lookup depth query (add depth e.1 e.2 (ofWeighted depth entries)) = _
    rw [lookup_add depth query e.1 e.2 _ hq ha, ih hr]
    simp [eq_comm, Nat.add_comm]

end CountTrie

end InducedPentagons.Paper

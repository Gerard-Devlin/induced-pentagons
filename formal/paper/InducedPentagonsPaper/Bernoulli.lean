module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

public section
noncomputable section
open scoped BigOperators

namespace InducedPentagons.Paper

def bernoulliFactor (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def bernoulliWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (b : ι → Bool) : ℝ :=
  ∏ i, bernoulliFactor (p i) (b i)

def bernoulliExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (p : ι → ℝ) : ℝ := ∑ b, bernoulliWeight p b * f b

theorem bernoulliWeight_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (b : ι → Bool) : 0 ≤ bernoulliWeight p b := by
  apply Finset.prod_nonneg
  intro i _
  cases b i <;> simp only [bernoulliFactor, Bool.false_eq_true, ite_false, ite_true]
  · linarith [(hp i).2]
  · exact (hp i).1

theorem bernoulliWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    ∑ b, bernoulliWeight p b = 1 := by
  classical
  unfold bernoulliWeight
  rw [← Fintype.prod_sum]
  simp [bernoulliFactor]

theorem bernoulliExtension_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} {p : ι → ℝ} {bound : ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hf : ∀ b, f b ≤ bound) :
    bernoulliExtension f p ≤ bound := by
  unfold bernoulliExtension
  calc
    _ ≤ ∑ b, bernoulliWeight p b * bound :=
      Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hf b)
        (bernoulliWeight_nonnegative hp b))
    _ = bound := by rw [← Finset.sum_mul, bernoulliWeight_sum, one_mul]

def literalIndicator (q : Option Bool) (b : Bool) : ℝ :=
  match q with
  | none => 1
  | some required => if b = required then 1 else 0

def patternIndicator {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → Option Bool)
    (b : ι → Bool) : ℝ := ∏ i, literalIndicator (q i) (b i)

def patternValue {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → Option Bool) (p : ι → ℝ) : ℝ :=
  ∏ i, match q i with
    | none => 1
    | some true => p i
    | some false => 1 - p i

/-- Independent Bernoulli extension of a Boolean cylinder is precisely the
multilinear product of its required edges and nonedges. -/
theorem bernoulliExtension_pattern {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → Option Bool) (p : ι → ℝ) :
    bernoulliExtension (patternIndicator q) p = patternValue q p := by
  classical
  unfold bernoulliExtension bernoulliWeight patternIndicator patternValue
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => bernoulliFactor (p i) b * literalIndicator (q i) b)]
  apply Finset.prod_congr rfl
  intro i _
  cases q i with
  | none => simp [bernoulliFactor, literalIndicator]
  | some b => cases b <;> simp [bernoulliFactor, literalIndicator]

/-- A finite sum of pattern monomials is the Bernoulli expectation of its
Boolean restriction. This is the multilinearity step in the profile envelope. -/
theorem bernoulliExtension_patterns {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (q : κ → ι → Option Bool) (p : ι → ℝ) :
    bernoulliExtension (fun b => ∑ k, patternIndicator (q k) b) p =
      ∑ k, patternValue (q k) p := by
  unfold bernoulliExtension
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => bernoulliExtension_pattern (q k) p)

theorem pattern_sum_le_of_boolean_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (q : κ → ι → Option Bool) {p : ι → ℝ} {bound : ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hbool : ∀ b, (∑ k, patternIndicator (q k) b) ≤ bound) :
    (∑ k, patternValue (q k) p) ≤ bound := by
  rw [← bernoulliExtension_patterns]
  exact bernoulliExtension_le hp hbool

end InducedPentagons.Paper

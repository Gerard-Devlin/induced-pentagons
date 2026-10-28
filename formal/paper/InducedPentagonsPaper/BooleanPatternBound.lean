module
public import InducedPentagonsPaper.Bernoulli

/-! A sound branching checker for upper bounds on sums of Boolean patterns.
It may stop at any node whose surviving pattern count is small enough. Its
soundness theorem covers every Boolean assignment, independently of the order
or completeness of the branching-variable list. -/

@[expose] public section
noncomputable section

namespace InducedPentagons.Paper

def acceptLiteral (q : Option Bool) (b : Bool) : Bool :=
  match q with
  | none => true
  | some required => required == b

def patternBound {α ι : Type*} (literal : α → ι → Option Bool) (bound : Nat) :
    List ι → List α → Bool
  | [], ps => decide (ps.length ≤ bound)
  | i :: rest, ps =>
      if ps.length ≤ bound then true else
        patternBound literal bound rest (ps.filter (fun p => acceptLiteral (literal p i) false)) &&
        patternBound literal bound rest (ps.filter (fun p => acceptLiteral (literal p i) true))

def patternTotal {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (ps : List α) (b : ι → Bool) : ℝ :=
  (ps.map (fun p => patternIndicator (literal p) b)).sum

theorem literalIndicator_bounds (q : Option Bool) (b : Bool) :
    0 ≤ literalIndicator q b ∧ literalIndicator q b ≤ 1 := by
  cases q with
  | none => norm_num [literalIndicator]
  | some required => cases required <;> cases b <;> norm_num [literalIndicator]

theorem patternIndicator_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → Option Bool) (b : ι → Bool) : patternIndicator q b ≤ 1 := by
  unfold patternIndicator
  apply Finset.prod_le_one₀
  · intro i _
    exact (literalIndicator_bounds (q i) (b i)).1
  · intro i _
    exact (literalIndicator_bounds (q i) (b i)).2

theorem literalIndicator_zero_of_reject (q : Option Bool) (b : Bool)
    (h : acceptLiteral q b = false) : literalIndicator q b = 0 := by
  cases q with
  | none => simp [acceptLiteral] at h
  | some required => cases required <;> cases b <;> simp_all [acceptLiteral, literalIndicator]

theorem patternIndicator_zero_of_reject {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → Option Bool) (b : ι → Bool) (i : ι)
    (h : acceptLiteral (q i) (b i) = false) : patternIndicator q b = 0 := by
  unfold patternIndicator
  exact Finset.prod_eq_zero (Finset.mem_univ i) (literalIndicator_zero_of_reject _ _ h)

theorem patternTotal_le_length {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (ps : List α) (b : ι → Bool) :
    patternTotal literal ps b ≤ (ps.length : ℝ) := by
  induction ps with
  | nil => simp [patternTotal]
  | cons p ps ih =>
    simp only [patternTotal, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one] at *
    linarith [patternIndicator_le_one (literal p) b]

theorem patternTotal_filter {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (ps : List α) (b : ι → Bool) (i : ι) :
    patternTotal literal (ps.filter (fun p => acceptLiteral (literal p i) (b i))) b =
      patternTotal literal ps b := by
  induction ps with
  | nil => simp [patternTotal]
  | cons p ps ih =>
    cases h : acceptLiteral (literal p i) (b i) with
    | false =>
      have hz := patternIndicator_zero_of_reject (literal p) b i h
      simpa [patternTotal, h, hz] using ih
    | true =>
      simpa [patternTotal, h] using congrArg (patternIndicator (literal p) b + ·) ih

theorem patternBound_sound {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (bound : Nat) (vars : List ι) (ps : List α)
    (h : patternBound literal bound vars ps = true) (b : ι → Bool) :
    patternTotal literal ps b ≤ (bound : ℝ) := by
  induction vars generalizing ps with
  | nil =>
    have hl : ps.length ≤ bound := of_decide_eq_true h
    exact (patternTotal_le_length literal ps b).trans (by exact_mod_cast hl)
  | cons i rest ih =>
    by_cases hl : ps.length ≤ bound
    · exact (patternTotal_le_length literal ps b).trans (by exact_mod_cast hl)
    · have hb := Bool.and_eq_true_iff.mp (by simpa only [patternBound, hl, ite_false] using h)
      have hs : patternBound literal bound rest
          (ps.filter (fun p => acceptLiteral (literal p i) (b i))) = true := by
        cases hi : b i with
        | false => simpa only [hi] using hb.1
        | true => simpa only [hi] using hb.2
      have hr := ih _ hs
      rw [patternTotal_filter] at hr
      exact hr

theorem bernoulliExtension_patternTotal {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (ps : List α) (x : ι → ℝ) :
    bernoulliExtension (patternTotal literal ps) x =
      (ps.map (fun p => patternValue (literal p) x)).sum := by
  induction ps with
  | nil => simp [patternTotal, bernoulliExtension]
  | cons p ps ih =>
    change bernoulliExtension (fun b => patternIndicator (literal p) b + patternTotal literal ps b) x =
      patternValue (literal p) x + (ps.map (fun p => patternValue (literal p) x)).sum
    unfold bernoulliExtension
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    change bernoulliExtension (patternIndicator (literal p)) x +
      bernoulliExtension (patternTotal literal ps) x = _
    rw [bernoulliExtension_pattern, ih]

/-- A successful Boolean branch check gives the fractional multilinear bound. -/
theorem patternBound_fractional {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (bound : Nat) (vars : List ι) (ps : List α)
    (h : patternBound literal bound vars ps = true) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (ps.map (fun p => patternValue (literal p) x)).sum ≤ (bound : ℝ) := by
  rw [← bernoulliExtension_patternTotal]
  exact bernoulliExtension_le hx (patternBound_sound literal bound vars ps h)

end InducedPentagons.Paper

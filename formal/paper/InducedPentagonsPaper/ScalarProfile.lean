module
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section

/-! The scalar optimization in Lemma 12.1. The graph-specific profile envelope
is an explicit hypothesis of the final corollary, rather than an axiom. -/

namespace InducedPentagons.Paper

def phasePenalty (u : ℝ) : ℝ := max (60 * u) (-20 * u)

def phaseCost (a : ℝ) : ℝ := 20 * (1 - a) * min (3 * a) 1

def profileCost (z : ℝ) : ℝ :=
  if z ≤ 1 then 60 * z * (1 - z) else 60 * (z - 1)

def periodicCost (x : ℝ) : ℝ := 60 * Int.fract x * (1 - Int.fract x)

theorem periodicCost_nonnegative (x : ℝ) : 0 ≤ periodicCost x := by
  unfold periodicCost
  exact mul_nonneg (mul_nonneg (by norm_num) (Int.fract_nonneg x))
    (sub_nonneg.mpr (Int.fract_lt_one x).le)

theorem periodicCost_add (x y : ℝ) :
    periodicCost (x + y) ≤ periodicCost x + periodicCost y := by
  have hx := Int.fract_nonneg x
  have hy := Int.fract_nonneg y
  have hx1 := Int.fract_lt_one x
  have hy1 := Int.fract_lt_one y
  rw [periodicCost, ← Int.fract_fract_add_fract]
  by_cases h : Int.fract x + Int.fract y < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith, h⟩]
    unfold periodicCost
    nlinarith [mul_nonneg hx hy]
  · have hf : Int.fract (Int.fract x + Int.fract y) =
        Int.fract x + Int.fract y - 1 := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by linarith, by linarith, 1, ?_⟩
      norm_num
    rw [hf]
    unfold periodicCost
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1.le) (sub_nonneg.mpr hy1.le)]

theorem periodicCost_sum (z : List ℝ) :
    periodicCost z.sum ≤ (z.map periodicCost).sum := by
  induction z with
  | nil => simp [periodicCost, Int.fract]
  | cons x xs ih =>
    simpa only [List.sum_cons, List.map_cons] using
      (periodicCost_add x xs.sum).trans (add_le_add (le_refl _) ih)

theorem periodicCost_le_profileCost {z : ℝ} (hz : 0 ≤ z) :
    periodicCost z ≤ profileCost z := by
  by_cases hz1 : z < 1
  · rw [profileCost, ite_eq_left hz1.le, periodicCost,
        Int.fract_eq_self.mpr ⟨hz, hz1⟩]
  · have hfloor : (1 : ℤ) ≤ ⌊z⌋ := Int.le_floor.mpr (by simpa using le_of_not_gt hz1)
    have hfloor' : (1 : ℝ) ≤ (⌊z⌋ : ℝ) := by exact_mod_cast hfloor
    have hf := Int.fract_nonneg z
    have hfs := Int.fract_add_floor z
    have hle : periodicCost z ≤ 60 * (z - 1) := by
      unfold periodicCost
      nlinarith [sq_nonneg (Int.fract z)]
    by_cases h : z ≤ 1
    · have heq : z = 1 := by linarith
      subst z
      norm_num [periodicCost, profileCost, Int.fract]
    · simpa [profileCost, h] using hle

theorem reduced_scalar_profile {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ell : ℤ) :
    phaseCost a ≤ 60 * t * (1 - t) + phasePenalty (a + ell - t) := by
  have hpA : phaseCost a ≤ 60 * a * (1 - a) := by
    have h := mul_le_mul_of_nonneg_left (min_le_left (3 * a) 1)
      (show 0 ≤ 20 * (1 - a) by linarith)
    unfold phaseCost
    nlinarith
  have hpB : phaseCost a ≤ 20 * (1 - a) := by
    simpa [phaseCost] using mul_le_mul_of_nonneg_left (min_le_right (3 * a) 1)
      (show 0 ≤ 20 * (1 - a) by linarith)
  have hq : 0 ≤ t * (1 - t) := mul_nonneg ht (sub_nonneg.mpr ht1)
  have hpL : 60 * (a + ell - t) ≤ phasePenalty (a + ell - t) := le_max_left _ _
  have hpR : -20 * (a + ell - t) ≤ phasePenalty (a + ell - t) := le_max_right _ _
  by_cases hn : ell ≤ -1
  · have hn' : (ell : ℝ) ≤ -1 := by exact_mod_cast hn
    nlinarith
  · by_cases hp : 1 ≤ ell
    · have hp' : (1 : ℝ) ≤ ell := by exact_mod_cast hp
      nlinarith [sq_nonneg a]
    · have heq : ell = 0 := by omega
      subst ell
      simp only [Int.cast_zero, add_zero] at hpL hpR ⊢
      by_cases hta : t ≤ a
      · nlinarith [mul_nonneg (sub_nonneg.mpr hta) (add_nonneg ha ht)]
      · by_cases hphase : 3 * a ≤ 1
        · have hprod : 0 ≤ (t - a) * (4 - 3 * t - 3 * a) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
        · have hprod : 0 ≤ (1 - t) * (3 * t - 1) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith

/-- The scalar optimization for arbitrary nonnegative profile sizes, including
sizes above one and arbitrary integer offsets. -/
theorem scalar_profile_cost (z : List ℝ) (hz : ∀ x ∈ z, 0 ≤ x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ell : ℤ) :
    phaseCost a ≤ (z.map profileCost).sum + phasePenalty (a + ell - z.sum) := by
  have hs : periodicCost z.sum ≤ (z.map profileCost).sum := by
    apply (periodicCost_sum z).trans
    apply List.sum_le_sum
    intro x hx
    exact periodicCost_le_profileCost (hz x hx)
  have heq : a + (ell : ℝ) - z.sum =
      a + ((ell - ⌊z.sum⌋ : ℤ) : ℝ) - Int.fract z.sum := by
    push_cast
    linarith [Int.fract_add_floor z.sum]
  have h := reduced_scalar_profile ha ha1 (Int.fract_nonneg z.sum)
    (Int.fract_lt_one z.sum).le (ell - ⌊z.sum⌋)
  rw [heq]
  exact h.trans (add_le_add hs (le_refl _))

theorem profileCost_le_linkDeficit {d c : ℝ} (_hd : 0 ≤ d)
    (hcq : c ≤ (12 / 5 : ℝ) * d ^ 2) (hc60 : c ≤ 60) :
    profileCost (d / 5) ≤ 12 * d - c := by
  unfold profileCost
  split_ifs <;> nlinarith

/-- Equation (58) from the two explicit profile-envelope inequalities.
For each pair, the first coordinate is d(p) and the second is c(p). -/
theorem scalar_profile (profiles : List (ℝ × ℝ))
    (henv : ∀ p ∈ profiles,
      0 ≤ p.1 ∧ p.2 ≤ (12 / 5 : ℝ) * p.1 ^ 2 ∧ p.2 ≤ 60)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ell : ℤ) :
    phaseCost a ≤ (profiles.map (fun p => 12 * p.1 - p.2)).sum +
      phasePenalty (a + ell - (profiles.map (fun p => p.1 / 5)).sum) := by
  have hz : ∀ x ∈ profiles.map (fun p => p.1 / 5), 0 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    exact div_nonneg (henv p hp).1 (by norm_num)
  apply (scalar_profile_cost _ hz ha ha1 ell).trans
  apply add_le_add _ (le_refl _)
  rw [List.map_map]
  apply List.sum_le_sum
  intro p hp
  exact profileCost_le_linkDeficit (henv p hp).1 (henv p hp).2.1 (henv p hp).2.2

end InducedPentagons.Paper

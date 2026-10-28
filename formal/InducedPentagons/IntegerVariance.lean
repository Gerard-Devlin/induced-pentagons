import InducedPentagons.Soundness

/-! Elementary integer-lattice facts used in class-imbalance arguments. -/

namespace InducedPentagons

def integerSum : List Int → Int
  | [] => 0
  | x :: xs => x + integerSum xs

def squareSum : List Int → Int
  | [] => 0
  | x :: xs => x * x + squareSum xs

theorem squareSum_nonnegative (xs : List Int) : 0 <= squareSum xs := by
  induction xs with
  | nil => decide
  | cons x xs ih => exact Int.add_nonneg (integer_square_nonnegative x) ih

theorem square_parity (x : Int) : (x * x) % 2 = x % 2 := by
  have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rw [Int.mul_emod]
  rcases h with h | h <;> simp [h]

theorem squareSum_parity (xs : List Int) : squareSum xs % 2 = integerSum xs % 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (x * x + squareSum xs) % 2 = (x + integerSum xs) % 2
    rw [Int.add_emod (x * x) (squareSum xs) 2,
      Int.add_emod x (integerSum xs) 2, square_parity, ih]

theorem squareSum_zero_iff (xs : List Int) :
    squareSum xs = 0 ↔ ∀ x ∈ xs, x = 0 := by
  constructor
  · intro h
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx : x = 0 := positive_square_vanishes (weight := 1)
        (by decide) (squareSum_nonnegative xs) (by simpa [squareSum] using h)
      have ht : squareSum xs = 0 := by simpa [squareSum, hx] using h
      intro y hy
      rcases List.mem_cons.mp hy with hy | hy
      · exact hy ▸ hx
      · exact ih ht y hy
  · intro h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, y = 0 := fun y hy => h y (by simp [hy])
      simp [squareSum, hx, ih ht]

/-- A nonzero balanced integral deviation has squared norm at least two. -/
theorem balanced_integer_variance_gap (xs : List Int) (balanced : integerSum xs = 0)
    (nonzero : ∃ x ∈ xs, x ≠ 0) : 2 <= squareSum xs := by
  have nonnegative := squareSum_nonnegative xs
  have parity : squareSum xs % 2 = 0 := by rw [squareSum_parity, balanced]; rfl
  have notzero : squareSum xs ≠ 0 := by
    intro h
    obtain ⟨x, hx, hnx⟩ := nonzero
    exact hnx ((squareSum_zero_iff xs).mp h x hx)
  omega

end InducedPentagons

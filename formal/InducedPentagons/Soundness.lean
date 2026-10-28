import InducedPentagons.Verifier

/-! Elementary ordered-integer consequences of a positive SOS decomposition.
These lemmas do not identify the imported tensors with graph densities. -/

namespace InducedPentagons

theorem integer_square_nonnegative (x : Int) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Int.mul_nonneg hx hx
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

def weightedSquares : List Int → List Int → Int
  | w :: ws, x :: xs => w * (x * x) + weightedSquares ws xs
  | _, _ => 0

theorem weightedSquares_nonnegative (weights values : List Int)
    (positive : ∀ w ∈ weights, 0 <= w) : 0 <= weightedSquares weights values := by
  induction weights generalizing values with
  | nil => simp [weightedSquares]
  | cons w ws ih =>
    cases values with
    | nil => simp [weightedSquares]
    | cons x xs =>
      simp only [weightedSquares]
      apply Int.add_nonneg
      · exact Int.mul_nonneg (positive w (by simp)) (integer_square_nonnegative x)
      · exact ih xs (fun q hq => positive q (by simp [hq]))

theorem positive_square_vanishes {weight value remainder : Int}
    (weight_positive : 0 < weight) (remainder_nonnegative : 0 <= remainder)
    (identity : weight * (value * value) + remainder = 0) : value = 0 := by
  have nonnegative := Int.mul_nonneg (Int.le_of_lt weight_positive)
    (integer_square_nonnegative value)
  have product_zero : weight * (value * value) = 0 := by omega
  have square_zero : value * value = 0 :=
    (Int.mul_eq_zero.mp product_zero).resolve_left (by omega)
  exact (Int.mul_eq_zero.mp square_zero).elim id id

end InducedPentagons

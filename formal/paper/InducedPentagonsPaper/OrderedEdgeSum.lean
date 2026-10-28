import InducedPentagonsPaper.WeightedGraph

open scoped BigOperators

namespace InducedPentagons.Paper

noncomputable def orderedEdgeSum {V : Type} [Fintype V] [LinearOrder V]
    (g : Graph V) (x : V → ℝ) : ℝ :=
  ∑ u, ∑ v, if u < v then if g.adj u v = true then x u * x v else 0 else 0

theorem dart_sum_eq_doubleSum {V : Type} [Fintype V] (g : Graph V) (x : V → ℝ) :
    (∑ p : Darts g, x p.val.1 * x p.val.2) =
      ∑ u, ∑ v, if g.adj u v = true then x u * x v else 0 := by
  classical
  change (∑ p : {p : V × V // g.adj p.1 p.2 = true}, x p.val.1 * x p.val.2) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : V × V => g.adj p.1 p.2 = true))
    (by simp) (fun p : V × V => x p.1 * x p.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem edgeMass_eq_orderedEdgeSum {V : Type} [Fintype V] [LinearOrder V]
    (g : Graph V) (x : V → ℝ) : edgeMass g x = orderedEdgeSum g x := by
  let f : V → V → ℝ := fun u v => if g.adj u v = true then x u * x v else 0
  have hs : ∀ u v, f u v = f v u := by
    intro u v
    simp only [f, g.symmetric u v, mul_comm]
  have hd : ∀ u, f u u = 0 := by intro u; simp [f, g.loopless]
  have hsplit : (∑ u, ∑ v, f u v) =
      (∑ u, ∑ v, if u < v then f u v else 0) +
      (∑ u, ∑ v, if v < u then f u v else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases lt_trichotomy u v with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst v; simp [hd]
    · simp [h, not_lt_of_ge h.le]
  have hswap : (∑ u, ∑ v, if v < u then f u v else 0) =
      ∑ u, ∑ v, if u < v then f u v else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hs v u]
  unfold edgeMass
  rw [dart_sum_eq_doubleSum]
  change (∑ u, ∑ v, f u v) / 2 = _
  change (∑ u, ∑ v, f u v) / 2 = ∑ u, ∑ v, if u < v then f u v else 0
  rw [hswap] at hsplit
  linarith

theorem sum_finRange {M : Type*} [AddCommMonoid M] {n : Nat} (f : Fin n → M) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  rw [← List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

theorem list_sum_filter_map {V M : Type*} [AddCommMonoid M]
    (l : List V) (p : V → Bool) (f : V → M) :
    ((l.filter p).map f).sum = (l.map (fun v => if p v then f v else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : p a <;> simp [h, ih]

theorem list_sum_flatMap {V M : Type*} [AddCommMonoid M]
    (l : List V) (f : V → List M) :
    (l.flatMap f).sum = (l.map (fun v => (f v).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

end InducedPentagons.Paper

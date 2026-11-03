import InducedPentagonsPaper.JointFlagPermutation
import InducedPentagonsPaper.FlagProductSemantics

/-! Exact full-permutation probabilities for the five certificate flag bases. -/

namespace InducedPentagons.Paper

/-- A permutation realizes two prescribed rooted flag isomorphism types. -/
def FullPermutationFlagPairHasTypes {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (g : Graph (Fin n)) (i j : Fin dimension) (e : Equiv.Perm (Fin n)) : Prop :=
  JointFlagPairHasTypes hn typeMask basis g i j (jointFlagSampleOfPermutation hn e)

theorem fullPermutationFlagPairCount_semantics {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (classify : Graph (Fin (roots + free)) → Fin dimension)
    (hclassify : ∀ g, rootTypeCheck roots typeMask g = true → ∀ i,
      classify g = i ↔ Nonempty (RootedGraphEquiv roots g
        (maskGraph (roots + free) basis[i])))
    (g : Graph (Fin n)) (i j : Fin dimension) :
    Nat.card {e : Equiv.Perm (Fin n) //
      FullPermutationFlagPairHasTypes hn typeMask basis g i j e} =
      jointFlagPairCount hn (jointRootCheck (free := free) typeMask g)
        (fun x => classify (x.graph g)) i j * free.factorial ^ 2 := by
  change Nat.card {e : Equiv.Perm (Fin n) //
    JointFlagPairHasTypes hn typeMask basis g i j (jointFlagSampleOfPermutation hn e)} = _
  rw [jointFlagFullPermutation_predicate_card,
    ← jointFlagPairCount_semantics hn typeMask basis classify hclassify g i j]

theorem fullPermutationFlagPairProbability_semantics {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (typeMask : Nat) (basis : Vector Nat dimension)
    (classify : Graph (Fin (roots + free)) → Fin dimension)
    (hclassify : ∀ g, rootTypeCheck roots typeMask g = true → ∀ i,
      classify g = i ↔ Nonempty (RootedGraphEquiv roots g
        (maskGraph (roots + free) basis[i])))
    (g : Graph (Fin n)) (i j : Fin dimension) :
    (Nat.card {e : Equiv.Perm (Fin n) //
      FullPermutationFlagPairHasTypes hn typeMask basis g i j e} : ℚ) / n.factorial =
      (jointFlagPairCount hn (jointRootCheck (free := free) typeMask g)
        (fun x => classify (x.graph g)) i j : ℚ) /
          (n.descFactorial roots * (n - roots).choose free) := by
  change (Nat.card {e : Equiv.Perm (Fin n) //
    JointFlagPairHasTypes hn typeMask basis g i j (jointFlagSampleOfPermutation hn e)} : ℚ) /
      n.factorial = _
  rw [jointFlagFullPermutation_probability,
    ← jointFlagPairCount_semantics hn typeMask basis classify hclassify g i j]

theorem flagProductCount_one_root_permutations (g : Graph (Fin 7)) (i j : Fin 20) :
    Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 1) (free := 3)
      (by decide) 0 indexedFlagBasis_one_root g i j e} =
      flagProductCount_one_root g i j * 36 := by
  have h := (fullPermutationFlagPairCount_semantics (n := 7) (roots := 1) (free := 3)
      (by decide) 0 indexedFlagBasis_one_root indexedFlag_one_root
      indexedFlag_one_root_eq_iff g i j)
  norm_num [flagProductCount_one_root, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_one_root_permutation_probability (g : Graph (Fin 7)) (i j : Fin 20) :
    (Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 1) (free := 3)
      (by decide) 0 indexedFlagBasis_one_root g i j e} : ℚ) / 5040 =
      (flagProductCount_one_root g i j : ℚ) / 140 := by
  have h := (fullPermutationFlagPairProbability_semantics (n := 7) (roots := 1) (free := 3)
      (by decide) 0 indexedFlagBasis_one_root indexedFlag_one_root
      indexedFlag_one_root_eq_iff g i j)
  norm_num [flagProductCount_one_root, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_independent3_permutations (g : Graph (Fin 7)) (i j : Fin 72) :
    Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 0 indexedFlagBasis_independent3 g i j e} =
      flagProductCount_independent3 g i j * 4 := by
  have h := (fullPermutationFlagPairCount_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 0 indexedFlagBasis_independent3 indexedFlag_independent3
      indexedFlag_independent3_eq_iff g i j)
  norm_num [flagProductCount_independent3, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_independent3_permutation_probability (g : Graph (Fin 7)) (i j : Fin 72) :
    (Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 0 indexedFlagBasis_independent3 g i j e} : ℚ) / 5040 =
      (flagProductCount_independent3 g i j : ℚ) / 1260 := by
  have h := (fullPermutationFlagPairProbability_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 0 indexedFlagBasis_independent3 indexedFlag_independent3
      indexedFlag_independent3_eq_iff g i j)
  norm_num [flagProductCount_independent3, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_edge_isolate_permutations (g : Graph (Fin 7)) (i j : Fin 72) :
    Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 1 indexedFlagBasis_edge_isolate g i j e} =
      flagProductCount_edge_isolate g i j * 4 := by
  have h := (fullPermutationFlagPairCount_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 1 indexedFlagBasis_edge_isolate indexedFlag_edge_isolate
      indexedFlag_edge_isolate_eq_iff g i j)
  norm_num [flagProductCount_edge_isolate, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_edge_isolate_permutation_probability (g : Graph (Fin 7)) (i j : Fin 72) :
    (Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 1 indexedFlagBasis_edge_isolate g i j e} : ℚ) / 5040 =
      (flagProductCount_edge_isolate g i j : ℚ) / 1260 := by
  have h := (fullPermutationFlagPairProbability_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 1 indexedFlagBasis_edge_isolate indexedFlag_edge_isolate
      indexedFlag_edge_isolate_eq_iff g i j)
  norm_num [flagProductCount_edge_isolate, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_path3_permutations (g : Graph (Fin 7)) (i j : Fin 72) :
    Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 17 indexedFlagBasis_path3 g i j e} =
      flagProductCount_path3 g i j * 4 := by
  have h := (fullPermutationFlagPairCount_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 17 indexedFlagBasis_path3 indexedFlag_path3
      indexedFlag_path3_eq_iff g i j)
  norm_num [flagProductCount_path3, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_path3_permutation_probability (g : Graph (Fin 7)) (i j : Fin 72) :
    (Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 17 indexedFlagBasis_path3 g i j e} : ℚ) / 5040 =
      (flagProductCount_path3 g i j : ℚ) / 1260 := by
  have h := (fullPermutationFlagPairProbability_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 17 indexedFlagBasis_path3 indexedFlag_path3
      indexedFlag_path3_eq_iff g i j)
  norm_num [flagProductCount_path3, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_triangle3_permutations (g : Graph (Fin 7)) (i j : Fin 72) :
    Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 19 indexedFlagBasis_triangle3 g i j e} =
      flagProductCount_triangle3 g i j * 4 := by
  have h := (fullPermutationFlagPairCount_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 19 indexedFlagBasis_triangle3 indexedFlag_triangle3
      indexedFlag_triangle3_eq_iff g i j)
  norm_num [flagProductCount_triangle3, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

theorem flagProductCount_triangle3_permutation_probability (g : Graph (Fin 7)) (i j : Fin 72) :
    (Nat.card {e : Equiv.Perm (Fin 7) // FullPermutationFlagPairHasTypes (roots := 3) (free := 2)
      (by decide) 19 indexedFlagBasis_triangle3 g i j e} : ℚ) / 5040 =
      (flagProductCount_triangle3 g i j : ℚ) / 1260 := by
  have h := (fullPermutationFlagPairProbability_semantics (n := 7) (roots := 3) (free := 2)
      (by decide) 19 indexedFlagBasis_triangle3 indexedFlag_triangle3
      indexedFlag_triangle3_eq_iff g i j)
  norm_num [flagProductCount_triangle3, Nat.factorial, Nat.descFactorial, Nat.choose] at h ⊢
  exact h

end InducedPentagons.Paper



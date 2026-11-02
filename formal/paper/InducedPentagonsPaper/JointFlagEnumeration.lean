import InducedPentagonsPaper.JointFlagGraphs
import InducedPentagonsPaper.PatternNormalization
import Mathlib.Data.Finset.Sigma

/-! Complete executable joint-sample enumeration without repeated deduplication. -/

namespace InducedPentagons.Paper

def flagRootFunctions (n roots : Nat) : List (Fin roots → Fin n) :=
  patternPrefixes (unconstrainedPattern roots) (maskGraph n 0) roots

theorem mem_flagRootFunctions (n roots : Nat) (f : Fin roots → Fin n) :
    f ∈ flagRootFunctions n roots ↔ Function.Injective f := by
  rw [flagRootFunctions, mem_patternPrefixes]
  simp [PrefixSatisfies, unconstrainedPattern]

def flagRootEmbeddingOfMember {n roots : Nat}
    (f : {f // f ∈ flagRootFunctions n roots}) : Fin roots ↪ Fin n :=
  ⟨f.val, (mem_flagRootFunctions n roots f.val).mp f.property⟩

def flagRootEmbeddingList (n roots : Nat) : List (Fin roots ↪ Fin n) :=
  (flagRootFunctions n roots).attach.map flagRootEmbeddingOfMember

theorem flagRootEmbeddingList_nodup (n roots : Nat) :
    (flagRootEmbeddingList n roots).Nodup := by
  apply List.Nodup.map _ ((patternPrefixes_nodup
    (unconstrainedPattern roots) (maskGraph n 0) roots).attach)
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun f : Fin roots ↪ Fin n => f.toFun) hab

def flagRootEmbeddingFinset (n roots : Nat) : Finset (Fin roots ↪ Fin n) :=
  ⟨flagRootEmbeddingList n roots, flagRootEmbeddingList_nodup n roots⟩

theorem mem_flagRootEmbeddingFinset {n roots : Nat} (f : Fin roots ↪ Fin n) :
    f ∈ flagRootEmbeddingFinset n roots := by
  change f ∈ flagRootEmbeddingList n roots
  apply List.mem_map.mpr
  refine ⟨⟨f.toFun, (mem_flagRootFunctions n roots f.toFun).mpr f.injective⟩, by simp, ?_⟩
  rfl

def jointLeftChoices {n roots : Nat} (free : Nat) (f : Fin roots ↪ Fin n) :
    Finset {s : Finset (Fin n) // s ⊆ (flagRootVertices f)ᶜ ∧ s.card = free} :=
  ((flagRootVertices f)ᶜ.powersetCard free).attach.map {
    toFun := fun s => ⟨s.val, Finset.mem_powersetCard.mp s.property⟩
    inj' := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : {s : Finset (Fin n) //
        s ⊆ (flagRootVertices f)ᶜ ∧ s.card = free} => z.val) hab
  }

theorem mem_jointLeftChoices {n roots free : Nat} (f : Fin roots ↪ Fin n)
    (s : {s : Finset (Fin n) // s ⊆ (flagRootVertices f)ᶜ ∧ s.card = free}) :
    s ∈ jointLeftChoices free f := by
  apply Finset.mem_map.mpr
  refine ⟨⟨s.val, Finset.mem_powersetCard.mpr s.property⟩, by simp, ?_⟩
  rfl

def jointFlagSamples (n roots free : Nat) : Finset (JointFlagSample n roots free) :=
  (flagRootEmbeddingFinset n roots).sigma (jointLeftChoices free)

theorem mem_jointFlagSamples {n roots free : Nat} (x : JointFlagSample n roots free) :
    x ∈ jointFlagSamples n roots free :=
  Finset.mem_sigma.mpr ⟨mem_flagRootEmbeddingFinset x.1, mem_jointLeftChoices x.1 x.2⟩

theorem jointFlagSamples_eq_univ (n roots free : Nat) :
    jointFlagSamples n roots free = Finset.univ := by
  classical
  ext x
  simp only [mem_jointFlagSamples, Finset.mem_univ]

theorem jointFlagSamples_card (n roots free : Nat) :
    (jointFlagSamples n roots free).card =
      n.descFactorial roots * (n - roots).choose free := by
  rw [jointFlagSamples_eq_univ, Finset.card_univ, jointFlagSample_card]

def enumeratedJointFlagPairCount {n roots free dimension : Nat} (hn : n = roots + 2 * free)
    (valid : (Fin roots ↪ Fin n) → Bool) (classify : JointFlagSample n roots free → Fin dimension)
    (i j : Fin dimension) : Nat :=
  ((jointFlagSamples n roots free).filter (fun x => valid x.1 &&
    decide (classify x = i) && decide (classify (x.swap hn) = j))).card

theorem enumeratedJointFlagPairCount_eq {n roots free dimension : Nat}
    (hn : n = roots + 2 * free) (valid : (Fin roots ↪ Fin n) → Bool)
    (classify : JointFlagSample n roots free → Fin dimension) (i j : Fin dimension) :
    enumeratedJointFlagPairCount hn valid classify i j =
      jointFlagPairCount hn valid classify i j := by
  classical
  unfold enumeratedJointFlagPairCount jointFlagPairCount
  rw [jointFlagSamples_eq_univ, Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true_iff,
    decide_eq_true_eq, and_assoc]

end InducedPentagons.Paper

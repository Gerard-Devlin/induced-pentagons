import InducedPentagonsPaper.PentagonCount

/-! The ten symmetries of the five-cycle, checked as adjacency-preserving maps. -/

namespace InducedPentagons.Paper

def cycleGraph : Graph (Fin 5) where
  adj := cycleAdj
  symmetric := by decide +kernel
  loopless := by decide +kernel

abbrev CycleSymmetry := PentagonEmbedding cycleGraph

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cycleSymmetry_card : Fintype.card CycleSymmetry = 10 := by decide +kernel

theorem cycleSymmetry_bijective (f : CycleSymmetry) : Function.Bijective f.val :=
  ⟨inducedPentagon_injective f.property,
    Finite.surjective_of_injective (inducedPentagon_injective f.property)⟩

def cycleRotate (r i : Fin 5) : Fin 5 := ⟨(r.val + i.val) % 5, by omega⟩

def cycleReverseIndex (i : Fin 5) : Fin 5 := ⟨(5 - i.val) % 5, by omega⟩

theorem cycleRotate_pattern : ∀ r i j : Fin 5,
    cycleAdj (cycleRotate r i) (cycleRotate r j) = cycleAdj i j := by decide +kernel

theorem cycleRotate_surjective : ∀ r, Function.Surjective (cycleRotate r) := by
  decide +kernel

@[simp] theorem cycleRotate_zero (r : Fin 5) : cycleRotate r 0 = r := by
  fin_cases r <;> rfl

theorem cycleReverse_pattern : ∀ i j : Fin 5,
    cycleAdj (cycleReverseIndex i) (cycleReverseIndex j) = cycleAdj i j := by decide +kernel

theorem cycleReverse_surjective : Function.Surjective cycleReverseIndex := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cycle_rooted_self_maps : ∀ f : Fin 5 → Fin 5,
    f 0 = 0 → (∀ i j, cycleAdj (f i) (f j) = cycleAdj i j) →
      (∀ i, f i = i) ∨ (∀ i, f i = cycleReverseIndex i) := by decide +kernel

end InducedPentagons.Paper

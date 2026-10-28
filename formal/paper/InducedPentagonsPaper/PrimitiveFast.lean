import InducedPentagonsPaper.PrimitiveCounts
import InducedPentagonsPaper.PatternSteps

/-! Faster host-count checks with a proved ordered-constraint precondition. -/

namespace InducedPentagons.Paper

def orderedSpecsCheck (specs : List PrimitivePatternSpec) : Bool :=
  specs.all (fun p => p.pattern.edges.all (fun e => decide (e.1.val < e.2.val)) &&
    p.pattern.nonedges.all (fun e => decide (e.1.val < e.2.val)))

theorem orderedSpecsCheck_sound {specs : List PrimitivePatternSpec}
    (hs : orderedSpecsCheck specs = true) : ∀ p ∈ specs, OrderedPattern p.pattern := by
  simpa only [orderedSpecsCheck, OrderedPattern, List.all_eq_true, Bool.and_eq_true_iff,
    decide_eq_true_eq] using hs

def fastPrimitiveCounts (specs : List PrimitivePatternSpec) {n : Nat}
    (g : Graph (Fin n)) : List Nat :=
  specs.map (fun p => (fastPatternEnumeration p.pattern g).length)

theorem primitiveSemanticCounts_eq_fast (specs : List PrimitivePatternSpec)
    (hs : orderedSpecsCheck specs = true) {n : Nat} (g : Graph (Fin n)) :
    primitiveSemanticCounts specs g = fastPrimitiveCounts specs g := by
  unfold primitiveSemanticCounts fastPrimitiveCounts
  apply List.map_congr_left
  intro p hp
  exact fastPatternEnumeration_count (orderedSpecsCheck_sound hs p hp) g

def fastPrimitiveRowCheck (specs : List PrimitivePatternSpec) (h : HostRow) : Bool :=
  h.primitive.toList == fastPrimitiveCounts specs (maskGraph 7 h.mask)

theorem fastPrimitiveRowCheck_sound (specs : List PrimitivePatternSpec)
    (hs : orderedSpecsCheck specs = true) (h : HostRow)
    (hh : fastPrimitiveRowCheck specs h = true) :
    h.primitive.toList = primitiveSemanticCounts specs (maskGraph 7 h.mask) := by
  rw [primitiveSemanticCounts_eq_fast specs hs]
  exact of_decide_eq_true (by simpa [fastPrimitiveRowCheck] using hh)

end InducedPentagons.Paper

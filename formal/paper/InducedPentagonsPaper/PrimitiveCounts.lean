import InducedPentagonsPaper.PatternEnumeration
import InducedPentagons.Verifier

/-! Semantic interpretation of the primitive-count array in each certificate host. -/

namespace InducedPentagons.Paper

structure PrimitivePatternSpec where
  name : String
  vertices : Nat
  pattern : PartialPattern vertices

def primitiveSemanticCounts (specs : List PrimitivePatternSpec) {n : Nat}
    (g : Graph (Fin n)) : List Nat :=
  specs.map (fun p => patternInjectionCount p.pattern g)

def primitiveEnumeratedCounts (specs : List PrimitivePatternSpec) {n : Nat}
    (g : Graph (Fin n)) : List Nat :=
  specs.map (fun p => (patternInjectionEnumeration p.pattern g).length)

theorem primitiveSemanticCounts_eq_enumerated (specs : List PrimitivePatternSpec) {n : Nat}
    (g : Graph (Fin n)) : primitiveSemanticCounts specs g = primitiveEnumeratedCounts specs g := by
  unfold primitiveSemanticCounts primitiveEnumeratedCounts
  apply List.map_congr_left
  intro p _
  exact patternInjectionCount_eq_enumeration_length p.pattern g

def primitiveRowCheck (specs : List PrimitivePatternSpec) (h : HostRow) : Bool :=
  h.primitive.toList == primitiveEnumeratedCounts specs (maskGraph 7 h.mask)

theorem primitiveRowCheck_sound (specs : List PrimitivePatternSpec) (h : HostRow)
    (hh : primitiveRowCheck specs h = true) :
    h.primitive.toList = primitiveSemanticCounts specs (maskGraph 7 h.mask) := by
  rw [primitiveSemanticCounts_eq_enumerated]
  exact of_decide_eq_true (by simpa [primitiveRowCheck] using hh)

end InducedPentagons.Paper

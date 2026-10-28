module
public import InducedPentagonsPaper.BooleanPatternBound

@[expose] public section

namespace InducedPentagons.Paper

structure ProfileMask where
  required : Nat
  excluded : Nat
  deriving Repr, DecidableEq

def maskLiteral (p : ProfileMask) (i : Fin 16) : Option Bool :=
  if p.required.testBit i.val then some true
  else if p.excluded.testBit i.val then some false
  else none

end InducedPentagons.Paper

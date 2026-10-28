import InducedPentagons.Verifier

/-!
The Gram matrix is a sum of weighted outer products. Computing an entire
upper row at once avoids repeating kernel reductions of array indexing.
All summands remain explicit integers and all equality checks use the kernel.
-/

namespace InducedPentagons

def gramUpperRow (c : Certificate) (b i : Nat) : List Int :=
  c.squares.toList.foldl (fun row s =>
    if s.block == b then
      let weight := s.coefficient.scaled * s.vector[i]!
      row.zipWith (· + ·) (s.vector.toList.drop i |>.map (fun value => weight * value))
    else row) (List.replicate (c.blocks[b]!.masks.size - i) 0)

def checkGramRowFast (c : Certificate) (g : GramData) (b i : Nat) : Bool :=
  b < c.blocks.size && i < c.blocks[b]!.masks.size && g.size == 5 &&
  g[b]!.size == c.blocks[b]!.masks.size &&
  g[b]![i]!.size == c.blocks[b]!.masks.size - i &&
  g[b]![i]!.toList == gramUpperRow c b i

end InducedPentagons

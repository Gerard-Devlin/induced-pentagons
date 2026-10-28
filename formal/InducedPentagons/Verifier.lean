import Std

/-!
Exact integer verification of the supplied finite SOS and equality-span data.
The normalizations below are the explicit formulas in Sections 2 and 4.
This module does not assert that the imported tensors count graphs correctly,
nor does it formalize graphon integration or the analytic arguments.
-/

namespace InducedPentagons

structure Coefficient where
  label : String
  numerator : Int
  denominator : Nat
  scaled : Int
  deriving Repr, Inhabited

structure SquareSource where
  id : String
  block : Nat
  coefficient : Coefficient
  vector : Array Int
  deriving Repr, Inhabited

structure FlagBlock where
  masks : Array Nat
  denominator : Nat
  kernel : Array (Array Int)
  deriving Repr, Inhabited

structure Certificate where
  scale : Nat
  dataDenominator : Nat
  hosts : Array Nat
  fixedMasks : Array Nat
  patternDenominators : Array Nat
  free : Array Coefficient
  positive : Array Coefficient
  squares : Array SquareSource
  slacks : Array Coefficient
  blocks : Array FlagBlock
  deriving Repr, Inhabited

structure TensorEntry where
  block : Nat
  i : Nat
  j : Nat
  count : Nat
  deriving Repr, Inhabited

structure HostRow where
  index : Nat
  mask : Nat
  primitive : Array Nat
  induced : Array Nat
  complement : Array Nat
  tensor : Array TensorEntry
  deriving Repr, Inhabited

structure SpanTerm where
  source : Nat
  sourceName : String
  extra : Nat
  coefficient : Coefficient
  deriving Repr, Inhabited

structure SpanWitness where
  kind : Nat
  scale : Nat
  indices : Array Nat
  terms : Array SpanTerm
  target : Array Coefficient
  deriving Repr, Inhabited

def intSum (xs : Array Int) : Int := xs.toList.foldl (· + ·) 0

def dot (xs ys : Array Int) : Int :=
  (xs.toList.zipWith (· * ·) ys.toList).foldl (· + ·) 0

def checkCoefficient (scale : Nat) (q : Coefficient) : Bool :=
  q.denominator > 0 && q.numerator * (scale : Int) == q.scaled * (q.denominator : Int)

def strictlySorted (xs : Array Nat) : Bool :=
  (xs.toList.zip xs.toList.tail).all fun p => p.1 < p.2

def checkSquare (c : Certificate) (s : SquareSource) : Bool :=
  s.block < c.blocks.size && checkCoefficient c.scale s.coefficient &&
  s.coefficient.scaled > 0 && s.vector.size == c.blocks[s.block]!.masks.size &&
  s.vector.toList.any (· != 0) &&
  c.blocks[s.block]!.kernel.toList.all (fun row =>
    row.size == s.vector.size && dot row s.vector == 0)

/-- The same fixed injection denominators as `src/proof_specification.py`. -/
def expectedPatternDenominators : Array Nat :=
  #[42, 2520, 5040, 5040, 5040, 210, 840, 840, 5040, 840,
    840, 5040, 5040, 840, 5040, 5040, 5040, 5040, 5040, 5040, 5040, 840]

def checkNormalization (c : Certificate) : Bool :=
  (#[(5, 144 * 5040), (5, 663552 * 210), (5, 663552 * 840),
     (1, 9216 * 840), (1, 2 * 5040), (1, 5040), (1, 2520),
     (1, 663552), (1, 3024), (1, 140), (1, 1260)] : Array (Nat × Nat)).all
    (fun q => (c.dataDenominator * q.1) % q.2 == 0)

def checkMetadata (c : Certificate) : Bool :=
  c.scale > 0 && c.dataDenominator == 557383680 && checkNormalization c &&
  c.hosts.size == 1044 && strictlySorted c.hosts &&
  c.hosts.all (· < 2 ^ 21) &&
  c.fixedMasks.size == 34 && strictlySorted c.fixedMasks &&
  c.fixedMasks.all (· < 1024) &&
  c.patternDenominators == expectedPatternDenominators &&
  c.free.size == 37 && c.positive.size == 4 &&
  c.slacks.size == 1044 && c.squares.size == 184 && c.blocks.size == 5 &&
  c.free.toList.all (checkCoefficient c.scale) &&
  c.positive.toList.all (fun q => checkCoefficient c.scale q && q.scaled >= 0) &&
  c.slacks.toList.all (fun q => checkCoefficient c.scale q && q.scaled >= 0) &&
  (c.slacks.toList.filter (fun q => q.scaled > 0)).length == 826 &&
  c.squares.toList.all (checkSquare c) &&
  ((c.squares.map (·.id)).toList.eraseDups.length == 184) &&
  c.free[0]!.label == "Phi1" && c.free[1]!.label == "Phi2" &&
  c.free[2]!.label == "Phi3" &&
  ((List.range 34).all fun j => c.free[j + 3]!.label == s!"density_{c.fixedMasks[j]!}") &&
  (c.positive.map (·.label)) == #["PhiTri", "Ji0", "Ji1", "Jdel"] &&
  (c.blocks.map (fun b => b.masks.size)) == #[20, 72, 72, 72, 72] &&
  (c.blocks.map (·.denominator)) == #[140, 1260, 1260, 1260, 1260] &&
  c.blocks.all (fun b => strictlySorted b.masks) &&
  ((List.range 5).all fun b => c.blocks[b]!.masks.all (· < (if b == 0 then 64 else 1024))) &&
  (-(1157 : Int) * (c.scale : Int) < 10 * c.free[0]!.scaled) &&
  c.free[0]!.scaled < 0 && c.free[2]!.scaled < 0 &&
  c.free[1]!.scaled + c.free[2]!.scaled > 310 * (c.scale : Int) &&
  216 * (c.scale : Int) * (c.free[1]!.scaled + c.free[2]!.scaled) >
    5 * c.free[0]!.scaled * c.free[0]!.scaled

/-- Upper-triangular storage; multiplication of the square coordinates commutes. -/
def triangularIndex (d i j : Nat) : Nat := i * (2 * d + 1 - i) / 2 + j - i

abbrev GramData := Array (Array (Array Int))

def gramAt (_c : Certificate) (g : GramData) (b i j : Nat) : Int :=
  g[b]![min i j]![max i j - min i j]!

def gramEntry (c : Certificate) (b i j : Nat) : Int :=
  c.squares.toList.foldl (fun n s => if s.block == b then
    n + s.coefficient.scaled * s.vector[i]! * s.vector[j]! else n) 0

def checkGramRow (c : Certificate) (g : GramData) (b i : Nat) : Bool :=
  b < c.blocks.size && i < c.blocks[b]!.masks.size &&
  g.size == 5 &&
  g[b]!.size == c.blocks[b]!.masks.size &&
  g[b]![i]!.size == c.blocks[b]!.masks.size - i &&
  (List.range (c.blocks[b]!.masks.size - i)).all (fun k =>
    gramAt c g b i (i + k) == gramEntry c b i (i + k))

/-- A raw partially induced pattern, scaled by the common data denominator. -/
def patternTerm (c : Certificate) (h : HostRow) (i : Nat) (n : Int) (d : Nat) : Int :=
  (h.primitive[i]! : Int) *
    ((c.dataDenominator : Int) * n / (d * c.patternDenominators[i]! : Nat))

def freeColumns (c : Certificate) (h : HostRow) : Array Int :=
  #[patternTerm c h 2 5 144 - patternTerm c h 5 5 663552,
    patternTerm c h 3 5 144 - patternTerm c h 6 5 663552,
    patternTerm c h 4 5 144 - patternTerm c h 7 5 663552] ++
  (List.range 34).toArray.map (fun j =>
    (144 * Int.ofNat h.complement[j]! - 5 * Int.ofNat h.induced[j]!) *
      (c.dataDenominator / 3024 : Nat))

def positiveColumns (c : Certificate) (h : HostRow) : Array Int :=
  #[patternTerm c h 8 5 144 - patternTerm c h 9 5 663552,
    patternTerm c h 11 1 1 - patternTerm c h 12 1 1 - patternTerm c h 10 1 9216,
    patternTerm c h 14 1 1 - patternTerm c h 15 1 1 - patternTerm c h 13 1 9216,
    patternTerm c h 16 1 2 - patternTerm c h 21 1 9216 -
      intSum ((List.range 4).toArray.map (fun j => patternTerm c h (17 + j) 1 2))]

def hostLeft (c : Certificate) (h : HostRow) : Int :=
  (((c.dataDenominator * 5 / 663552 : Nat) : Int) - patternTerm c h 1 1 1) * (c.scale : Int)

def hostRight (c : Certificate) (g : GramData) (h : HostRow) : Int :=
  dot (freeColumns c h) (c.free.map (·.scaled)) +
  dot (positiveColumns c h) (c.positive.map (·.scaled)) +
  h.tensor.toList.foldl (fun n e => n + (e.count : Int) * gramAt c g e.block e.i e.j *
    (c.dataDenominator / c.blocks[e.block]!.denominator : Nat)) 0 +
  c.slacks[h.index]!.scaled * (c.dataDenominator : Int)

def checkHost (c : Certificate) (g : GramData) (h : HostRow) : Bool :=
  h.index < 1044 && h.mask == c.hosts[h.index]! &&
  h.primitive.size == 22 && h.induced.size == 34 && h.complement.size == 34 &&
  h.tensor.toList.all (fun e => e.block < 5 && e.i <= e.j &&
    e.j < c.blocks[e.block]!.masks.size && e.count > 0) &&
  hostLeft c h == hostRight c g h

def checkHostChunk (c : Certificate) (g : GramData)
    (start : Nat) (rows : Array HostRow) : Bool :=
  start < 1044 && start % 12 == 0 && rows.size == min 12 (1044 - start) &&
  (List.range rows.size).all (fun i => rows[i]!.index == start + i &&
    checkHost c g rows[i]!)

/-- Lexicographic edge-bit encoding on five labelled vertices. -/
def edge5 (mask a b : Nat) : Int :=
  if a == b then 0 else
    let i := min a b
    let j := max a b
    if mask.testBit (i * (9 - i) / 2 + j - i - 1) then 1 else 0

def triangle5 (mask : Nat) : Bool :=
  (List.range 5).any (fun a => (List.range 5).any (fun b =>
    (List.range 5).any (fun d => a < b && b < d &&
      edge5 mask a b * edge5 mask a d * edge5 mask b d == 1)))

def degreeVector (mask root : Nat) : Int :=
  24 * (edge5 mask root 3 + edge5 mask root 4) - 5

def codegreeVector (mask root : Nat) : Int :=
  5 * (edge5 mask root 3 * edge5 mask 2 3 + edge5 mask root 4 * edge5 mask 2 4) -
    2 * (edge5 mask 2 3 + edge5 mask 2 4)

def spanBlock (w : SpanWitness) : Nat := if w.kind <= 1 then 3 else 2

def spanSource (c : Certificate) (_w : SpanWitness) (t : SpanTerm) (i : Nat) : Int :=
  if t.extra == 0 then c.squares[t.source]!.vector[i]!
  else degreeVector c.blocks[2]!.masks[i]! (t.extra - 1)

def validSpanTerm (c : Certificate) (w : SpanWitness) (t : SpanTerm) : Bool :=
  checkCoefficient w.scale t.coefficient &&
  (if t.extra == 0 then t.source < c.squares.size &&
    t.sourceName == c.squares[t.source]!.id &&
    c.squares[t.source]!.block == spanBlock w &&
    c.squares[t.source]!.coefficient.scaled > 0
  else w.kind >= 2 && (t.extra == 1 || t.extra == 2) &&
    t.sourceName == s!"degree_identity_{t.extra - 1}")

def expectedSpanIndices (c : Certificate) (w : SpanWitness) : Array Nat :=
  (List.range c.blocks[spanBlock w]!.masks.size).toArray.filter (fun i =>
    w.kind == 0 || !triangle5 c.blocks[spanBlock w]!.masks[i]!)

def spanTarget (c : Certificate) (w : SpanWitness) (i : Nat) : Int :=
  if w.kind == 0 then w.target[i]!.scaled else
    (w.scale : Int) * (if w.kind == 1 then degreeVector c.blocks[3]!.masks[i]! 1
    else codegreeVector c.blocks[2]!.masks[i]! (w.kind - 2))

def checkSpan (c : Certificate) (w : SpanWitness) : Bool :=
  w.kind < 4 && w.scale > 0 && w.indices == expectedSpanIndices c w &&
  w.indices.size == (if w.kind == 0 then 72 else if w.kind == 1 then 24 else 32) &&
  w.terms.toList.all (validSpanTerm c w) &&
  (if w.kind == 0 then w.target.size == 72 &&
    w.target.all (checkCoefficient w.scale) &&
    w.indices.all (fun i => if triangle5 c.blocks[3]!.masks[i]! then
      w.target[i]!.scaled >= (w.scale : Int) else w.target[i]!.scaled == 0)
   else true) &&
  w.indices.all (fun i =>
    w.terms.toList.foldl (fun n t => n + t.coefficient.scaled * spanSource c w t i) 0 ==
      spanTarget c w i)

/-- Soundness of adding nonnegative summands after the free part vanishes. -/
theorem nonnegative_certificate {lhs free positive squares slack : Int}
    (identity : lhs = free + positive + squares + slack)
    (free_zero : free = 0) (positive_nonnegative : 0 <= positive)
    (squares_nonnegative : 0 <= squares) (slack_nonnegative : 0 <= slack) :
    0 <= lhs := by omega

end InducedPentagons

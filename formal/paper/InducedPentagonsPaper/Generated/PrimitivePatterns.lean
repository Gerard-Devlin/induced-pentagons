import InducedPentagonsPaper.PrimitiveFast

namespace InducedPentagons.Paper

def primitivePattern00 : PartialPattern 2 where
  edges := [(0, 1)]
  nonedges := []

def primitivePattern01 : PartialPattern 5 where
  edges := [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)]
  nonedges := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]

def primitivePattern02 : PartialPattern 6 where
  edges := [(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4)]
  nonedges := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]

def primitivePattern03 : PartialPattern 7 where
  edges := [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (2, 3), (3, 4)]
  nonedges := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]

def primitivePattern04 : PartialPattern 7 where
  edges := [(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4), (5, 6)]
  nonedges := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]

def primitivePattern05 : PartialPattern 3 where
  edges := [(0, 1), (0, 2)]
  nonedges := []

def primitivePattern06 : PartialPattern 4 where
  edges := [(0, 1), (0, 2), (0, 3)]
  nonedges := []

def primitivePattern07 : PartialPattern 4 where
  edges := [(0, 1), (1, 2), (2, 3)]
  nonedges := []

def primitivePattern08 : PartialPattern 7 where
  edges := [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (2, 3), (3, 4), (5, 6)]
  nonedges := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]

def primitivePattern09 : PartialPattern 4 where
  edges := [(0, 1), (0, 2), (0, 3), (1, 2)]
  nonedges := []

def primitivePattern10 : PartialPattern 4 where
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]
  nonedges := [(2, 3)]

def primitivePattern11 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 6), (4, 5), (5, 6)]
  nonedges := [(0, 5), (0, 6), (1, 4), (1, 5), (2, 3), (4, 6)]

def primitivePattern12 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (5, 6)]
  nonedges := [(0, 5), (1, 6), (2, 3), (4, 5), (4, 6)]

def primitivePattern13 : PartialPattern 4 where
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  nonedges := []

def primitivePattern14 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 6), (2, 3), (4, 5), (5, 6)]
  nonedges := [(0, 5), (0, 6), (1, 4), (1, 5), (4, 6)]

def primitivePattern15 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (5, 6)]
  nonedges := [(0, 5), (1, 6), (4, 5), (4, 6)]

def primitivePattern16 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 6), (1, 2), (3, 4), (4, 5), (5, 6)]
  nonedges := [(0, 4), (0, 5), (3, 5), (3, 6), (4, 6)]

def primitivePattern17 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 6), (1, 2), (3, 4), (4, 5), (5, 6)]
  nonedges := [(0, 4), (0, 5), (1, 3), (1, 6), (3, 5), (3, 6), (4, 6)]

def primitivePattern18 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 5), (3, 4), (4, 5), (5, 6)]
  nonedges := [(0, 4), (1, 3), (1, 6), (3, 5), (3, 6), (4, 6)]

def primitivePattern19 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 4), (3, 4), (4, 5), (5, 6)]
  nonedges := [(0, 5), (1, 3), (1, 6), (3, 5), (3, 6), (4, 6)]

def primitivePattern20 : PartialPattern 7 where
  edges := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 4), (1, 5), (3, 4), (4, 5), (5, 6)]
  nonedges := [(1, 3), (1, 6), (3, 5), (3, 6), (4, 6)]

def primitivePattern21 : PartialPattern 4 where
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]
  nonedges := []

def primitivePatternSpecs : List PrimitivePatternSpec := [
  ⟨"p", 2, primitivePattern00⟩,
  ⟨"theta", 5, primitivePattern01⟩,
  ⟨"L1", 6, primitivePattern02⟩,
  ⟨"L2", 7, primitivePattern03⟩,
  ⟨"L3", 7, primitivePattern04⟩,
  ⟨"B1", 3, primitivePattern05⟩,
  ⟨"B2", 4, primitivePattern06⟩,
  ⟨"B3", 4, primitivePattern07⟩,
  ⟨"L_triangle", 7, primitivePattern08⟩,
  ⟨"B_triangle", 4, primitivePattern09⟩,
  ⟨"R0", 4, primitivePattern10⟩,
  ⟨"J0_A", 7, primitivePattern11⟩,
  ⟨"J0_B", 7, primitivePattern12⟩,
  ⟨"R1", 4, primitivePattern13⟩,
  ⟨"J1_A", 7, primitivePattern14⟩,
  ⟨"J1_B", 7, primitivePattern15⟩,
  ⟨"Jdel_Lg", 7, primitivePattern16⟩,
  ⟨"Jdel_Lf00", 7, primitivePattern17⟩,
  ⟨"Jdel_Lf01", 7, primitivePattern18⟩,
  ⟨"Jdel_Lf10", 7, primitivePattern19⟩,
  ⟨"Jdel_Lf11", 7, primitivePattern20⟩,
  ⟨"Ddel", 4, primitivePattern21⟩
]

theorem primitivePatternSpecs_count : primitivePatternSpecs.length = 22 := by decide +kernel

theorem primitivePatternSpecs_ordered : orderedSpecsCheck primitivePatternSpecs = true := by decide +kernel

theorem primitivePattern_denominators :
    primitivePatternSpecs.map (fun p => Nat.descFactorial 7 p.vertices) =
      expectedPatternDenominators.toList := by decide +kernel

end InducedPentagons.Paper

import InducedPentagonsPaper.FlagIndex
import InducedPentagonsPaper.Generated.FlagSeparation

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def indexedFlagBasis_one_root : Vector Nat 20 := #v[0, 1, 3, 7, 8, 9, 11, 12, 13, 15, 24, 25, 26, 27, 30, 31, 56, 57, 59, 63]

def indexedFlagData_one_root : Vector (IndexedFlagWitness 20) 64 := #v[
  ⟨⟨0, 0, 1672⟩, 0⟩,
  ⟨⟨1, 1, 1672⟩, 1⟩,
  ⟨⟨2, 1, 1616⟩, 1⟩,
  ⟨⟨3, 3, 1672⟩, 2⟩,
  ⟨⟨4, 1, 720⟩, 1⟩,
  ⟨⟨5, 3, 1224⟩, 2⟩,
  ⟨⟨6, 3, 1112⟩, 2⟩,
  ⟨⟨7, 7, 1672⟩, 3⟩,
  ⟨⟨8, 8, 1672⟩, 4⟩,
  ⟨⟨9, 9, 1672⟩, 5⟩,
  ⟨⟨10, 9, 1616⟩, 5⟩,
  ⟨⟨11, 11, 1672⟩, 6⟩,
  ⟨⟨12, 12, 1672⟩, 7⟩,
  ⟨⟨13, 13, 1672⟩, 8⟩,
  ⟨⟨14, 13, 1616⟩, 8⟩,
  ⟨⟨15, 15, 1672⟩, 9⟩,
  ⟨⟨16, 8, 1224⟩, 4⟩,
  ⟨⟨17, 9, 1224⟩, 5⟩,
  ⟨⟨18, 12, 1224⟩, 7⟩,
  ⟨⟨19, 13, 1224⟩, 8⟩,
  ⟨⟨20, 9, 720⟩, 5⟩,
  ⟨⟨21, 11, 1224⟩, 6⟩,
  ⟨⟨22, 13, 720⟩, 8⟩,
  ⟨⟨23, 15, 1224⟩, 9⟩,
  ⟨⟨24, 24, 1672⟩, 10⟩,
  ⟨⟨25, 25, 1672⟩, 11⟩,
  ⟨⟨26, 26, 1672⟩, 12⟩,
  ⟨⟨27, 27, 1672⟩, 13⟩,
  ⟨⟨28, 26, 1224⟩, 12⟩,
  ⟨⟨29, 27, 1224⟩, 13⟩,
  ⟨⟨30, 30, 1672⟩, 14⟩,
  ⟨⟨31, 31, 1672⟩, 15⟩,
  ⟨⟨32, 8, 1112⟩, 4⟩,
  ⟨⟨33, 12, 1112⟩, 7⟩,
  ⟨⟨34, 9, 1112⟩, 5⟩,
  ⟨⟨35, 13, 1112⟩, 8⟩,
  ⟨⟨36, 9, 664⟩, 5⟩,
  ⟨⟨37, 13, 664⟩, 8⟩,
  ⟨⟨38, 11, 1112⟩, 6⟩,
  ⟨⟨39, 15, 1112⟩, 9⟩,
  ⟨⟨40, 24, 1616⟩, 10⟩,
  ⟨⟨41, 26, 1616⟩, 12⟩,
  ⟨⟨42, 25, 1616⟩, 11⟩,
  ⟨⟨43, 27, 1616⟩, 13⟩,
  ⟨⟨44, 26, 1112⟩, 12⟩,
  ⟨⟨45, 30, 1616⟩, 14⟩,
  ⟨⟨46, 27, 1112⟩, 13⟩,
  ⟨⟨47, 31, 1616⟩, 15⟩,
  ⟨⟨48, 24, 720⟩, 10⟩,
  ⟨⟨49, 26, 720⟩, 12⟩,
  ⟨⟨50, 26, 664⟩, 12⟩,
  ⟨⟨51, 30, 720⟩, 14⟩,
  ⟨⟨52, 25, 720⟩, 11⟩,
  ⟨⟨53, 27, 720⟩, 13⟩,
  ⟨⟨54, 27, 664⟩, 13⟩,
  ⟨⟨55, 31, 720⟩, 15⟩,
  ⟨⟨56, 56, 1672⟩, 16⟩,
  ⟨⟨57, 57, 1672⟩, 17⟩,
  ⟨⟨58, 57, 1616⟩, 17⟩,
  ⟨⟨59, 59, 1672⟩, 18⟩,
  ⟨⟨60, 57, 720⟩, 17⟩,
  ⟨⟨61, 59, 1224⟩, 18⟩,
  ⟨⟨62, 59, 1112⟩, 18⟩,
  ⟨⟨63, 63, 1672⟩, 19⟩
]

def indexedFlagLookup_one_root (m : Fin 64) : IndexedFlagWitness 20 :=
  indexedFlagData_one_root[m]

theorem indexedFlagBasis_one_root_toList : indexedFlagBasis_one_root.toList = flagBasis_one_root := by
  decide +kernel

theorem indexedFlagBasis_one_root_injective :
    Function.Injective (fun i : Fin 20 => indexedFlagBasis_one_root[i]) := by
  decide +kernel

theorem indexedFlagBasis_one_root_certificate :
    indexedFlagBasis_one_root.toList = (Generated.certificate.blocks[0]!).masks.toList := by
  rw [indexedFlagBasis_one_root_toList]
  exact flag_basis_one_root_certificate

theorem indexedFlagBasis_one_root_certificateAt : ∀ i : Fin 20,
    indexedFlagBasis_one_root[i] = (Generated.certificate.blocks[0]!).masks[i.val]! := by
  decide +kernel

theorem indexedFlagBasis_one_root_separated :
    RootedFlagBasisSeparated 4 1 indexedFlagBasis_one_root.toList := by
  rw [indexedFlagBasis_one_root_toList]
  exact flag_basis_one_root_separated

theorem indexedFlagLookup_one_root_checked :
    flagIndexLookupCheck 4 6 1 0 indexedFlagBasis_one_root indexedFlagLookup_one_root = true := by
  decide +kernel

def indexedFlag_one_root (g : Graph (Fin 4)) : Fin 20 :=
  flagIndex 6 indexedFlagLookup_one_root g

theorem indexedFlag_one_root_sound (g : Graph (Fin 4))
    (hg : rootTypeCheck 1 0 g = true) :
    Nonempty (RootedGraphEquiv 1 g (maskGraph 4 indexedFlagBasis_one_root[indexedFlag_one_root g])) :=
  flagIndex_sound edgeIndexSeparated_four edgeIndexBounded_four indexedFlagLookup_one_root_checked g hg

theorem indexedFlag_one_root_eq_iff (g : Graph (Fin 4))
    (hg : rootTypeCheck 1 0 g = true) (j : Fin 20) :
    indexedFlag_one_root g = j ↔
      Nonempty (RootedGraphEquiv 1 g (maskGraph 4 indexedFlagBasis_one_root[j])) :=
  flagIndex_eq_iff edgeIndexSeparated_four edgeIndexBounded_four
    indexedFlagLookup_one_root_checked indexedFlagBasis_one_root_separated
    indexedFlagBasis_one_root_injective g hg j

theorem indexedFlag_one_root_isomorphic {g h : Graph (Fin 4)}
    (hg : rootTypeCheck 1 0 g = true) (hh : rootTypeCheck 1 0 h = true)
    (e : RootedGraphEquiv 1 g h) : indexedFlag_one_root g = indexedFlag_one_root h :=
  flagIndex_isomorphic edgeIndexSeparated_four edgeIndexBounded_four
    indexedFlagLookup_one_root_checked indexedFlagBasis_one_root_separated
    indexedFlagBasis_one_root_injective hg hh e

end InducedPentagons.Paper

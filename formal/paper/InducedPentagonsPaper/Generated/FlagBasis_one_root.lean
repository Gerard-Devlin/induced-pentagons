import InducedPentagonsPaper.RootedFlags
import InducedPentagons.Generated.Inputs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def flagBasis_one_root : List Nat := [0, 1, 3, 7, 8, 9, 11, 12, 13, 15, 24, 25, 26, 27, 30, 31, 56, 57, 59, 63]

def flagWitnesses_one_root : List RootedFlagWitness := [
  ⟨0, 0, 1672⟩,
  ⟨1, 1, 1672⟩,
  ⟨2, 1, 1616⟩,
  ⟨3, 3, 1672⟩,
  ⟨4, 1, 720⟩,
  ⟨5, 3, 1224⟩,
  ⟨6, 3, 1112⟩,
  ⟨7, 7, 1672⟩,
  ⟨8, 8, 1672⟩,
  ⟨9, 9, 1672⟩,
  ⟨10, 9, 1616⟩,
  ⟨11, 11, 1672⟩,
  ⟨12, 12, 1672⟩,
  ⟨13, 13, 1672⟩,
  ⟨14, 13, 1616⟩,
  ⟨15, 15, 1672⟩,
  ⟨16, 8, 1224⟩,
  ⟨17, 9, 1224⟩,
  ⟨18, 12, 1224⟩,
  ⟨19, 13, 1224⟩,
  ⟨20, 9, 720⟩,
  ⟨21, 11, 1224⟩,
  ⟨22, 13, 720⟩,
  ⟨23, 15, 1224⟩,
  ⟨24, 24, 1672⟩,
  ⟨25, 25, 1672⟩,
  ⟨26, 26, 1672⟩,
  ⟨27, 27, 1672⟩,
  ⟨28, 26, 1224⟩,
  ⟨29, 27, 1224⟩,
  ⟨30, 30, 1672⟩,
  ⟨31, 31, 1672⟩,
  ⟨32, 8, 1112⟩,
  ⟨33, 12, 1112⟩,
  ⟨34, 9, 1112⟩,
  ⟨35, 13, 1112⟩,
  ⟨36, 9, 664⟩,
  ⟨37, 13, 664⟩,
  ⟨38, 11, 1112⟩,
  ⟨39, 15, 1112⟩,
  ⟨40, 24, 1616⟩,
  ⟨41, 26, 1616⟩,
  ⟨42, 25, 1616⟩,
  ⟨43, 27, 1616⟩,
  ⟨44, 26, 1112⟩,
  ⟨45, 30, 1616⟩,
  ⟨46, 27, 1112⟩,
  ⟨47, 31, 1616⟩,
  ⟨48, 24, 720⟩,
  ⟨49, 26, 720⟩,
  ⟨50, 26, 664⟩,
  ⟨51, 30, 720⟩,
  ⟨52, 25, 720⟩,
  ⟨53, 27, 720⟩,
  ⟨54, 27, 664⟩,
  ⟨55, 31, 720⟩,
  ⟨56, 56, 1672⟩,
  ⟨57, 57, 1672⟩,
  ⟨58, 57, 1616⟩,
  ⟨59, 59, 1672⟩,
  ⟨60, 57, 720⟩,
  ⟨61, 59, 1224⟩,
  ⟨62, 59, 1112⟩,
  ⟨63, 63, 1672⟩
]

theorem flag_sources_one_root :
    flagWitnesses_one_root.map RootedFlagWitness.source =
      (List.range (2 ^ 6)).filter (fun m => rootTypeCheck 1 0 (maskGraph 4 m)) := by
  decide +kernel

theorem flag_witnesses_one_root_checked :
    flagWitnesses_one_root.all (rootedFlagRowCheck 4 1 flagBasis_one_root) = true := by
  decide +kernel

theorem flag_basis_one_root_certificate :
    flagBasis_one_root = (Generated.certificate.blocks[0]!).masks.toList := by
  decide +kernel

theorem flag_basis_one_root_count : flagBasis_one_root.length = 20 := by decide +kernel

theorem flag_basis_one_root_nodup : flagBasis_one_root.Nodup := by decide +kernel

theorem flag_basis_one_root_types_checked :
    flagBasis_one_root.all (fun m => rootTypeCheck 1 0 (maskGraph 4 m)) = true := by
  decide +kernel

theorem flag_basis_one_root_covers :
    RootedFlagBasisCovers 4 1 0 flagBasis_one_root :=
  rootedFlagBasisCovers_of_rows edgeIndexSeparated_four
    edgeIndexBounded_four flagBasis_one_root flagWitnesses_one_root
    flag_sources_one_root flag_witnesses_one_root_checked

theorem certificate_flag_basis_one_root_covers :
    RootedFlagBasisCovers 4 1 0
      (Generated.certificate.blocks[0]!).masks.toList := by
  rw [← flag_basis_one_root_certificate]
  exact flag_basis_one_root_covers

end InducedPentagons.Paper

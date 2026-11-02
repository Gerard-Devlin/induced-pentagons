import InducedPentagonsPaper.Generated.FlagBases
import InducedPentagonsPaper.RootedFlagSeparation

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def rootedPermutationCodes4 : List Nat := [1672, 1224, 1616, 720, 1112, 664]

theorem rootedPermutationCodes4_complete :
    RootedPermutationCodesComplete 4 1 rootedPermutationCodes4 := by
  unfold RootedPermutationCodesComplete
  decide +kernel

def rootedPermutationCodes5 : List Nat := [18056, 14472]

theorem rootedPermutationCodes5_complete :
    RootedPermutationCodesComplete 5 3 rootedPermutationCodes5 := by
  unfold RootedPermutationCodesComplete
  decide +kernel

theorem flag_basis_one_root_separation_checked :
    rootedBasisSeparatedCheck 4 1 rootedPermutationCodes4 flagBasis_one_root = true := by
  decide +kernel

theorem flag_basis_one_root_separated :
    RootedFlagBasisSeparated 4 1 flagBasis_one_root :=
  rootedBasisSeparatedCheck_sound rootedPermutationCodes4_complete
    flag_basis_one_root_separation_checked

theorem certificate_flag_basis_one_root_separated :
    RootedFlagBasisSeparated 4 1
      (Generated.certificate.blocks[0]!).masks.toList := by
  rw [← flag_basis_one_root_certificate]
  exact flag_basis_one_root_separated

theorem flag_basis_independent3_separation_checked :
    rootedBasisSeparatedCheck 5 3 rootedPermutationCodes5 flagBasis_independent3 = true := by
  decide +kernel

theorem flag_basis_independent3_separated :
    RootedFlagBasisSeparated 5 3 flagBasis_independent3 :=
  rootedBasisSeparatedCheck_sound rootedPermutationCodes5_complete
    flag_basis_independent3_separation_checked

theorem certificate_flag_basis_independent3_separated :
    RootedFlagBasisSeparated 5 3
      (Generated.certificate.blocks[1]!).masks.toList := by
  rw [← flag_basis_independent3_certificate]
  exact flag_basis_independent3_separated

theorem flag_basis_edge_isolate_separation_checked :
    rootedBasisSeparatedCheck 5 3 rootedPermutationCodes5 flagBasis_edge_isolate = true := by
  decide +kernel

theorem flag_basis_edge_isolate_separated :
    RootedFlagBasisSeparated 5 3 flagBasis_edge_isolate :=
  rootedBasisSeparatedCheck_sound rootedPermutationCodes5_complete
    flag_basis_edge_isolate_separation_checked

theorem certificate_flag_basis_edge_isolate_separated :
    RootedFlagBasisSeparated 5 3
      (Generated.certificate.blocks[2]!).masks.toList := by
  rw [← flag_basis_edge_isolate_certificate]
  exact flag_basis_edge_isolate_separated

theorem flag_basis_path3_separation_checked :
    rootedBasisSeparatedCheck 5 3 rootedPermutationCodes5 flagBasis_path3 = true := by
  decide +kernel

theorem flag_basis_path3_separated :
    RootedFlagBasisSeparated 5 3 flagBasis_path3 :=
  rootedBasisSeparatedCheck_sound rootedPermutationCodes5_complete
    flag_basis_path3_separation_checked

theorem certificate_flag_basis_path3_separated :
    RootedFlagBasisSeparated 5 3
      (Generated.certificate.blocks[3]!).masks.toList := by
  rw [← flag_basis_path3_certificate]
  exact flag_basis_path3_separated

theorem flag_basis_triangle3_separation_checked :
    rootedBasisSeparatedCheck 5 3 rootedPermutationCodes5 flagBasis_triangle3 = true := by
  decide +kernel

theorem flag_basis_triangle3_separated :
    RootedFlagBasisSeparated 5 3 flagBasis_triangle3 :=
  rootedBasisSeparatedCheck_sound rootedPermutationCodes5_complete
    flag_basis_triangle3_separation_checked

theorem certificate_flag_basis_triangle3_separated :
    RootedFlagBasisSeparated 5 3
      (Generated.certificate.blocks[4]!).masks.toList := by
  rw [← flag_basis_triangle3_certificate]
  exact flag_basis_triangle3_separated

theorem rootedWitnessCheck_rejects_moved_root :
    rootedWitnessCheck 4 1 0 0 1665 = false := by decide +kernel

theorem rootedWitnessCheck_rejects_wrong_adjacency :
    rootedWitnessCheck 4 1 0 1 1672 = false := by decide +kernel

end InducedPentagons.Paper

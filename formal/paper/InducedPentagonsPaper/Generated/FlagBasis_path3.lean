import InducedPentagonsPaper.RootedFlags
import InducedPentagons.Generated.Inputs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def flagBasis_path3 : List Nat := [17, 21, 29, 49, 53, 57, 61, 113, 117, 125, 145, 149, 153, 157, 177, 181, 185, 189, 209, 213, 217, 221, 241, 245, 249, 253, 401, 405, 413, 433, 437, 441, 445, 497, 501, 509, 529, 533, 541, 561, 565, 569, 573, 625, 629, 637, 657, 661, 665, 669, 689, 693, 697, 701, 721, 725, 729, 733, 753, 757, 761, 765, 913, 917, 925, 945, 949, 953, 957, 1009, 1013, 1021]

def flagWitnesses_path3 : List RootedFlagWitness := [
  ⟨17, 17, 18056⟩,
  ⟨21, 21, 18056⟩,
  ⟨25, 21, 14472⟩,
  ⟨29, 29, 18056⟩,
  ⟨49, 49, 18056⟩,
  ⟨53, 53, 18056⟩,
  ⟨57, 57, 18056⟩,
  ⟨61, 61, 18056⟩,
  ⟨81, 49, 14472⟩,
  ⟨85, 57, 14472⟩,
  ⟨89, 53, 14472⟩,
  ⟨93, 61, 14472⟩,
  ⟨113, 113, 18056⟩,
  ⟨117, 117, 18056⟩,
  ⟨121, 117, 14472⟩,
  ⟨125, 125, 18056⟩,
  ⟨145, 145, 18056⟩,
  ⟨149, 149, 18056⟩,
  ⟨153, 153, 18056⟩,
  ⟨157, 157, 18056⟩,
  ⟨177, 177, 18056⟩,
  ⟨181, 181, 18056⟩,
  ⟨185, 185, 18056⟩,
  ⟨189, 189, 18056⟩,
  ⟨209, 209, 18056⟩,
  ⟨213, 213, 18056⟩,
  ⟨217, 217, 18056⟩,
  ⟨221, 221, 18056⟩,
  ⟨241, 241, 18056⟩,
  ⟨245, 245, 18056⟩,
  ⟨249, 249, 18056⟩,
  ⟨253, 253, 18056⟩,
  ⟨273, 145, 14472⟩,
  ⟨277, 153, 14472⟩,
  ⟨281, 149, 14472⟩,
  ⟨285, 157, 14472⟩,
  ⟨305, 209, 14472⟩,
  ⟨309, 217, 14472⟩,
  ⟨313, 213, 14472⟩,
  ⟨317, 221, 14472⟩,
  ⟨337, 177, 14472⟩,
  ⟨341, 185, 14472⟩,
  ⟨345, 181, 14472⟩,
  ⟨349, 189, 14472⟩,
  ⟨369, 241, 14472⟩,
  ⟨373, 249, 14472⟩,
  ⟨377, 245, 14472⟩,
  ⟨381, 253, 14472⟩,
  ⟨401, 401, 18056⟩,
  ⟨405, 405, 18056⟩,
  ⟨409, 405, 14472⟩,
  ⟨413, 413, 18056⟩,
  ⟨433, 433, 18056⟩,
  ⟨437, 437, 18056⟩,
  ⟨441, 441, 18056⟩,
  ⟨445, 445, 18056⟩,
  ⟨465, 433, 14472⟩,
  ⟨469, 441, 14472⟩,
  ⟨473, 437, 14472⟩,
  ⟨477, 445, 14472⟩,
  ⟨497, 497, 18056⟩,
  ⟨501, 501, 18056⟩,
  ⟨505, 501, 14472⟩,
  ⟨509, 509, 18056⟩,
  ⟨529, 529, 18056⟩,
  ⟨533, 533, 18056⟩,
  ⟨537, 533, 14472⟩,
  ⟨541, 541, 18056⟩,
  ⟨561, 561, 18056⟩,
  ⟨565, 565, 18056⟩,
  ⟨569, 569, 18056⟩,
  ⟨573, 573, 18056⟩,
  ⟨593, 561, 14472⟩,
  ⟨597, 569, 14472⟩,
  ⟨601, 565, 14472⟩,
  ⟨605, 573, 14472⟩,
  ⟨625, 625, 18056⟩,
  ⟨629, 629, 18056⟩,
  ⟨633, 629, 14472⟩,
  ⟨637, 637, 18056⟩,
  ⟨657, 657, 18056⟩,
  ⟨661, 661, 18056⟩,
  ⟨665, 665, 18056⟩,
  ⟨669, 669, 18056⟩,
  ⟨689, 689, 18056⟩,
  ⟨693, 693, 18056⟩,
  ⟨697, 697, 18056⟩,
  ⟨701, 701, 18056⟩,
  ⟨721, 721, 18056⟩,
  ⟨725, 725, 18056⟩,
  ⟨729, 729, 18056⟩,
  ⟨733, 733, 18056⟩,
  ⟨753, 753, 18056⟩,
  ⟨757, 757, 18056⟩,
  ⟨761, 761, 18056⟩,
  ⟨765, 765, 18056⟩,
  ⟨785, 657, 14472⟩,
  ⟨789, 665, 14472⟩,
  ⟨793, 661, 14472⟩,
  ⟨797, 669, 14472⟩,
  ⟨817, 721, 14472⟩,
  ⟨821, 729, 14472⟩,
  ⟨825, 725, 14472⟩,
  ⟨829, 733, 14472⟩,
  ⟨849, 689, 14472⟩,
  ⟨853, 697, 14472⟩,
  ⟨857, 693, 14472⟩,
  ⟨861, 701, 14472⟩,
  ⟨881, 753, 14472⟩,
  ⟨885, 761, 14472⟩,
  ⟨889, 757, 14472⟩,
  ⟨893, 765, 14472⟩,
  ⟨913, 913, 18056⟩,
  ⟨917, 917, 18056⟩,
  ⟨921, 917, 14472⟩,
  ⟨925, 925, 18056⟩,
  ⟨945, 945, 18056⟩,
  ⟨949, 949, 18056⟩,
  ⟨953, 953, 18056⟩,
  ⟨957, 957, 18056⟩,
  ⟨977, 945, 14472⟩,
  ⟨981, 953, 14472⟩,
  ⟨985, 949, 14472⟩,
  ⟨989, 957, 14472⟩,
  ⟨1009, 1009, 18056⟩,
  ⟨1013, 1013, 18056⟩,
  ⟨1017, 1013, 14472⟩,
  ⟨1021, 1021, 18056⟩
]

theorem flag_sources_path3 :
    flagWitnesses_path3.map RootedFlagWitness.source =
      (List.range (2 ^ 10)).filter (fun m => rootTypeCheck 3 17 (maskGraph 5 m)) := by
  decide +kernel

theorem flag_witnesses_path3_checked :
    flagWitnesses_path3.all (rootedFlagRowCheck 5 3 flagBasis_path3) = true := by
  decide +kernel

theorem flag_basis_path3_certificate :
    flagBasis_path3 = (Generated.certificate.blocks[3]!).masks.toList := by
  decide +kernel

theorem flag_basis_path3_count : flagBasis_path3.length = 72 := by decide +kernel

theorem flag_basis_path3_nodup : flagBasis_path3.Nodup := by decide +kernel

theorem flag_basis_path3_types_checked :
    flagBasis_path3.all (fun m => rootTypeCheck 3 17 (maskGraph 5 m)) = true := by
  decide +kernel

theorem flag_basis_path3_covers :
    RootedFlagBasisCovers 5 3 17 flagBasis_path3 :=
  rootedFlagBasisCovers_of_rows edgeIndexSeparated_five
    edgeIndexBounded_five flagBasis_path3 flagWitnesses_path3
    flag_sources_path3 flag_witnesses_path3_checked

theorem certificate_flag_basis_path3_covers :
    RootedFlagBasisCovers 5 3 17
      (Generated.certificate.blocks[3]!).masks.toList := by
  rw [← flag_basis_path3_certificate]
  exact flag_basis_path3_covers

end InducedPentagons.Paper

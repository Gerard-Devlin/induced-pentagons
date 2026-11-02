import InducedPentagonsPaper.RootedFlags
import InducedPentagons.Generated.Inputs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def flagBasis_triangle3 : List Nat := [19, 23, 31, 51, 55, 59, 63, 115, 119, 127, 147, 151, 155, 159, 179, 183, 187, 191, 211, 215, 219, 223, 243, 247, 251, 255, 403, 407, 415, 435, 439, 443, 447, 499, 503, 511, 531, 535, 543, 563, 567, 571, 575, 627, 631, 639, 659, 663, 667, 671, 691, 695, 699, 703, 723, 727, 731, 735, 755, 759, 763, 767, 915, 919, 927, 947, 951, 955, 959, 1011, 1015, 1023]

def flagWitnesses_triangle3 : List RootedFlagWitness := [
  ⟨19, 19, 18056⟩,
  ⟨23, 23, 18056⟩,
  ⟨27, 23, 14472⟩,
  ⟨31, 31, 18056⟩,
  ⟨51, 51, 18056⟩,
  ⟨55, 55, 18056⟩,
  ⟨59, 59, 18056⟩,
  ⟨63, 63, 18056⟩,
  ⟨83, 51, 14472⟩,
  ⟨87, 59, 14472⟩,
  ⟨91, 55, 14472⟩,
  ⟨95, 63, 14472⟩,
  ⟨115, 115, 18056⟩,
  ⟨119, 119, 18056⟩,
  ⟨123, 119, 14472⟩,
  ⟨127, 127, 18056⟩,
  ⟨147, 147, 18056⟩,
  ⟨151, 151, 18056⟩,
  ⟨155, 155, 18056⟩,
  ⟨159, 159, 18056⟩,
  ⟨179, 179, 18056⟩,
  ⟨183, 183, 18056⟩,
  ⟨187, 187, 18056⟩,
  ⟨191, 191, 18056⟩,
  ⟨211, 211, 18056⟩,
  ⟨215, 215, 18056⟩,
  ⟨219, 219, 18056⟩,
  ⟨223, 223, 18056⟩,
  ⟨243, 243, 18056⟩,
  ⟨247, 247, 18056⟩,
  ⟨251, 251, 18056⟩,
  ⟨255, 255, 18056⟩,
  ⟨275, 147, 14472⟩,
  ⟨279, 155, 14472⟩,
  ⟨283, 151, 14472⟩,
  ⟨287, 159, 14472⟩,
  ⟨307, 211, 14472⟩,
  ⟨311, 219, 14472⟩,
  ⟨315, 215, 14472⟩,
  ⟨319, 223, 14472⟩,
  ⟨339, 179, 14472⟩,
  ⟨343, 187, 14472⟩,
  ⟨347, 183, 14472⟩,
  ⟨351, 191, 14472⟩,
  ⟨371, 243, 14472⟩,
  ⟨375, 251, 14472⟩,
  ⟨379, 247, 14472⟩,
  ⟨383, 255, 14472⟩,
  ⟨403, 403, 18056⟩,
  ⟨407, 407, 18056⟩,
  ⟨411, 407, 14472⟩,
  ⟨415, 415, 18056⟩,
  ⟨435, 435, 18056⟩,
  ⟨439, 439, 18056⟩,
  ⟨443, 443, 18056⟩,
  ⟨447, 447, 18056⟩,
  ⟨467, 435, 14472⟩,
  ⟨471, 443, 14472⟩,
  ⟨475, 439, 14472⟩,
  ⟨479, 447, 14472⟩,
  ⟨499, 499, 18056⟩,
  ⟨503, 503, 18056⟩,
  ⟨507, 503, 14472⟩,
  ⟨511, 511, 18056⟩,
  ⟨531, 531, 18056⟩,
  ⟨535, 535, 18056⟩,
  ⟨539, 535, 14472⟩,
  ⟨543, 543, 18056⟩,
  ⟨563, 563, 18056⟩,
  ⟨567, 567, 18056⟩,
  ⟨571, 571, 18056⟩,
  ⟨575, 575, 18056⟩,
  ⟨595, 563, 14472⟩,
  ⟨599, 571, 14472⟩,
  ⟨603, 567, 14472⟩,
  ⟨607, 575, 14472⟩,
  ⟨627, 627, 18056⟩,
  ⟨631, 631, 18056⟩,
  ⟨635, 631, 14472⟩,
  ⟨639, 639, 18056⟩,
  ⟨659, 659, 18056⟩,
  ⟨663, 663, 18056⟩,
  ⟨667, 667, 18056⟩,
  ⟨671, 671, 18056⟩,
  ⟨691, 691, 18056⟩,
  ⟨695, 695, 18056⟩,
  ⟨699, 699, 18056⟩,
  ⟨703, 703, 18056⟩,
  ⟨723, 723, 18056⟩,
  ⟨727, 727, 18056⟩,
  ⟨731, 731, 18056⟩,
  ⟨735, 735, 18056⟩,
  ⟨755, 755, 18056⟩,
  ⟨759, 759, 18056⟩,
  ⟨763, 763, 18056⟩,
  ⟨767, 767, 18056⟩,
  ⟨787, 659, 14472⟩,
  ⟨791, 667, 14472⟩,
  ⟨795, 663, 14472⟩,
  ⟨799, 671, 14472⟩,
  ⟨819, 723, 14472⟩,
  ⟨823, 731, 14472⟩,
  ⟨827, 727, 14472⟩,
  ⟨831, 735, 14472⟩,
  ⟨851, 691, 14472⟩,
  ⟨855, 699, 14472⟩,
  ⟨859, 695, 14472⟩,
  ⟨863, 703, 14472⟩,
  ⟨883, 755, 14472⟩,
  ⟨887, 763, 14472⟩,
  ⟨891, 759, 14472⟩,
  ⟨895, 767, 14472⟩,
  ⟨915, 915, 18056⟩,
  ⟨919, 919, 18056⟩,
  ⟨923, 919, 14472⟩,
  ⟨927, 927, 18056⟩,
  ⟨947, 947, 18056⟩,
  ⟨951, 951, 18056⟩,
  ⟨955, 955, 18056⟩,
  ⟨959, 959, 18056⟩,
  ⟨979, 947, 14472⟩,
  ⟨983, 955, 14472⟩,
  ⟨987, 951, 14472⟩,
  ⟨991, 959, 14472⟩,
  ⟨1011, 1011, 18056⟩,
  ⟨1015, 1015, 18056⟩,
  ⟨1019, 1015, 14472⟩,
  ⟨1023, 1023, 18056⟩
]

theorem flag_sources_triangle3 :
    flagWitnesses_triangle3.map RootedFlagWitness.source =
      (List.range (2 ^ 10)).filter (fun m => rootTypeCheck 3 19 (maskGraph 5 m)) := by
  decide +kernel

theorem flag_witnesses_triangle3_checked :
    flagWitnesses_triangle3.all (rootedFlagRowCheck 5 3 flagBasis_triangle3) = true := by
  decide +kernel

theorem flag_basis_triangle3_certificate :
    flagBasis_triangle3 = (Generated.certificate.blocks[4]!).masks.toList := by
  decide +kernel

theorem flag_basis_triangle3_count : flagBasis_triangle3.length = 72 := by decide +kernel

theorem flag_basis_triangle3_nodup : flagBasis_triangle3.Nodup := by decide +kernel

theorem flag_basis_triangle3_types_checked :
    flagBasis_triangle3.all (fun m => rootTypeCheck 3 19 (maskGraph 5 m)) = true := by
  decide +kernel

theorem flag_basis_triangle3_covers :
    RootedFlagBasisCovers 5 3 19 flagBasis_triangle3 :=
  rootedFlagBasisCovers_of_rows edgeIndexSeparated_five
    edgeIndexBounded_five flagBasis_triangle3 flagWitnesses_triangle3
    flag_sources_triangle3 flag_witnesses_triangle3_checked

theorem certificate_flag_basis_triangle3_covers :
    RootedFlagBasisCovers 5 3 19
      (Generated.certificate.blocks[4]!).masks.toList := by
  rw [← flag_basis_triangle3_certificate]
  exact flag_basis_triangle3_covers

end InducedPentagons.Paper

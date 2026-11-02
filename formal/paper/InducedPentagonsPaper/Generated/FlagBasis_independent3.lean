import InducedPentagonsPaper.RootedFlags
import InducedPentagons.Generated.Inputs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def flagBasis_independent3 : List Nat := [0, 4, 12, 32, 36, 40, 44, 96, 100, 108, 128, 132, 136, 140, 160, 164, 168, 172, 192, 196, 200, 204, 224, 228, 232, 236, 384, 388, 396, 416, 420, 424, 428, 480, 484, 492, 512, 516, 524, 544, 548, 552, 556, 608, 612, 620, 640, 644, 648, 652, 672, 676, 680, 684, 704, 708, 712, 716, 736, 740, 744, 748, 896, 900, 908, 928, 932, 936, 940, 992, 996, 1004]

def flagWitnesses_independent3 : List RootedFlagWitness := [
  ⟨0, 0, 18056⟩,
  ⟨4, 4, 18056⟩,
  ⟨8, 4, 14472⟩,
  ⟨12, 12, 18056⟩,
  ⟨32, 32, 18056⟩,
  ⟨36, 36, 18056⟩,
  ⟨40, 40, 18056⟩,
  ⟨44, 44, 18056⟩,
  ⟨64, 32, 14472⟩,
  ⟨68, 40, 14472⟩,
  ⟨72, 36, 14472⟩,
  ⟨76, 44, 14472⟩,
  ⟨96, 96, 18056⟩,
  ⟨100, 100, 18056⟩,
  ⟨104, 100, 14472⟩,
  ⟨108, 108, 18056⟩,
  ⟨128, 128, 18056⟩,
  ⟨132, 132, 18056⟩,
  ⟨136, 136, 18056⟩,
  ⟨140, 140, 18056⟩,
  ⟨160, 160, 18056⟩,
  ⟨164, 164, 18056⟩,
  ⟨168, 168, 18056⟩,
  ⟨172, 172, 18056⟩,
  ⟨192, 192, 18056⟩,
  ⟨196, 196, 18056⟩,
  ⟨200, 200, 18056⟩,
  ⟨204, 204, 18056⟩,
  ⟨224, 224, 18056⟩,
  ⟨228, 228, 18056⟩,
  ⟨232, 232, 18056⟩,
  ⟨236, 236, 18056⟩,
  ⟨256, 128, 14472⟩,
  ⟨260, 136, 14472⟩,
  ⟨264, 132, 14472⟩,
  ⟨268, 140, 14472⟩,
  ⟨288, 192, 14472⟩,
  ⟨292, 200, 14472⟩,
  ⟨296, 196, 14472⟩,
  ⟨300, 204, 14472⟩,
  ⟨320, 160, 14472⟩,
  ⟨324, 168, 14472⟩,
  ⟨328, 164, 14472⟩,
  ⟨332, 172, 14472⟩,
  ⟨352, 224, 14472⟩,
  ⟨356, 232, 14472⟩,
  ⟨360, 228, 14472⟩,
  ⟨364, 236, 14472⟩,
  ⟨384, 384, 18056⟩,
  ⟨388, 388, 18056⟩,
  ⟨392, 388, 14472⟩,
  ⟨396, 396, 18056⟩,
  ⟨416, 416, 18056⟩,
  ⟨420, 420, 18056⟩,
  ⟨424, 424, 18056⟩,
  ⟨428, 428, 18056⟩,
  ⟨448, 416, 14472⟩,
  ⟨452, 424, 14472⟩,
  ⟨456, 420, 14472⟩,
  ⟨460, 428, 14472⟩,
  ⟨480, 480, 18056⟩,
  ⟨484, 484, 18056⟩,
  ⟨488, 484, 14472⟩,
  ⟨492, 492, 18056⟩,
  ⟨512, 512, 18056⟩,
  ⟨516, 516, 18056⟩,
  ⟨520, 516, 14472⟩,
  ⟨524, 524, 18056⟩,
  ⟨544, 544, 18056⟩,
  ⟨548, 548, 18056⟩,
  ⟨552, 552, 18056⟩,
  ⟨556, 556, 18056⟩,
  ⟨576, 544, 14472⟩,
  ⟨580, 552, 14472⟩,
  ⟨584, 548, 14472⟩,
  ⟨588, 556, 14472⟩,
  ⟨608, 608, 18056⟩,
  ⟨612, 612, 18056⟩,
  ⟨616, 612, 14472⟩,
  ⟨620, 620, 18056⟩,
  ⟨640, 640, 18056⟩,
  ⟨644, 644, 18056⟩,
  ⟨648, 648, 18056⟩,
  ⟨652, 652, 18056⟩,
  ⟨672, 672, 18056⟩,
  ⟨676, 676, 18056⟩,
  ⟨680, 680, 18056⟩,
  ⟨684, 684, 18056⟩,
  ⟨704, 704, 18056⟩,
  ⟨708, 708, 18056⟩,
  ⟨712, 712, 18056⟩,
  ⟨716, 716, 18056⟩,
  ⟨736, 736, 18056⟩,
  ⟨740, 740, 18056⟩,
  ⟨744, 744, 18056⟩,
  ⟨748, 748, 18056⟩,
  ⟨768, 640, 14472⟩,
  ⟨772, 648, 14472⟩,
  ⟨776, 644, 14472⟩,
  ⟨780, 652, 14472⟩,
  ⟨800, 704, 14472⟩,
  ⟨804, 712, 14472⟩,
  ⟨808, 708, 14472⟩,
  ⟨812, 716, 14472⟩,
  ⟨832, 672, 14472⟩,
  ⟨836, 680, 14472⟩,
  ⟨840, 676, 14472⟩,
  ⟨844, 684, 14472⟩,
  ⟨864, 736, 14472⟩,
  ⟨868, 744, 14472⟩,
  ⟨872, 740, 14472⟩,
  ⟨876, 748, 14472⟩,
  ⟨896, 896, 18056⟩,
  ⟨900, 900, 18056⟩,
  ⟨904, 900, 14472⟩,
  ⟨908, 908, 18056⟩,
  ⟨928, 928, 18056⟩,
  ⟨932, 932, 18056⟩,
  ⟨936, 936, 18056⟩,
  ⟨940, 940, 18056⟩,
  ⟨960, 928, 14472⟩,
  ⟨964, 936, 14472⟩,
  ⟨968, 932, 14472⟩,
  ⟨972, 940, 14472⟩,
  ⟨992, 992, 18056⟩,
  ⟨996, 996, 18056⟩,
  ⟨1000, 996, 14472⟩,
  ⟨1004, 1004, 18056⟩
]

theorem flag_sources_independent3 :
    flagWitnesses_independent3.map RootedFlagWitness.source =
      (List.range (2 ^ 10)).filter (fun m => rootTypeCheck 3 0 (maskGraph 5 m)) := by
  decide +kernel

theorem flag_witnesses_independent3_checked :
    flagWitnesses_independent3.all (rootedFlagRowCheck 5 3 flagBasis_independent3) = true := by
  decide +kernel

theorem flag_basis_independent3_certificate :
    flagBasis_independent3 = (Generated.certificate.blocks[1]!).masks.toList := by
  decide +kernel

theorem flag_basis_independent3_count : flagBasis_independent3.length = 72 := by decide +kernel

theorem flag_basis_independent3_nodup : flagBasis_independent3.Nodup := by decide +kernel

theorem flag_basis_independent3_types_checked :
    flagBasis_independent3.all (fun m => rootTypeCheck 3 0 (maskGraph 5 m)) = true := by
  decide +kernel

theorem flag_basis_independent3_covers :
    RootedFlagBasisCovers 5 3 0 flagBasis_independent3 :=
  rootedFlagBasisCovers_of_rows edgeIndexSeparated_five
    edgeIndexBounded_five flagBasis_independent3 flagWitnesses_independent3
    flag_sources_independent3 flag_witnesses_independent3_checked

theorem certificate_flag_basis_independent3_covers :
    RootedFlagBasisCovers 5 3 0
      (Generated.certificate.blocks[1]!).masks.toList := by
  rw [← flag_basis_independent3_certificate]
  exact flag_basis_independent3_covers

end InducedPentagons.Paper

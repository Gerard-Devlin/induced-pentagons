import InducedPentagonsPaper.RootedFlags
import InducedPentagons.Generated.Inputs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def flagBasis_edge_isolate : List Nat := [1, 5, 13, 33, 37, 41, 45, 97, 101, 109, 129, 133, 137, 141, 161, 165, 169, 173, 193, 197, 201, 205, 225, 229, 233, 237, 385, 389, 397, 417, 421, 425, 429, 481, 485, 493, 513, 517, 525, 545, 549, 553, 557, 609, 613, 621, 641, 645, 649, 653, 673, 677, 681, 685, 705, 709, 713, 717, 737, 741, 745, 749, 897, 901, 909, 929, 933, 937, 941, 993, 997, 1005]

def flagWitnesses_edge_isolate : List RootedFlagWitness := [
  ⟨1, 1, 18056⟩,
  ⟨5, 5, 18056⟩,
  ⟨9, 5, 14472⟩,
  ⟨13, 13, 18056⟩,
  ⟨33, 33, 18056⟩,
  ⟨37, 37, 18056⟩,
  ⟨41, 41, 18056⟩,
  ⟨45, 45, 18056⟩,
  ⟨65, 33, 14472⟩,
  ⟨69, 41, 14472⟩,
  ⟨73, 37, 14472⟩,
  ⟨77, 45, 14472⟩,
  ⟨97, 97, 18056⟩,
  ⟨101, 101, 18056⟩,
  ⟨105, 101, 14472⟩,
  ⟨109, 109, 18056⟩,
  ⟨129, 129, 18056⟩,
  ⟨133, 133, 18056⟩,
  ⟨137, 137, 18056⟩,
  ⟨141, 141, 18056⟩,
  ⟨161, 161, 18056⟩,
  ⟨165, 165, 18056⟩,
  ⟨169, 169, 18056⟩,
  ⟨173, 173, 18056⟩,
  ⟨193, 193, 18056⟩,
  ⟨197, 197, 18056⟩,
  ⟨201, 201, 18056⟩,
  ⟨205, 205, 18056⟩,
  ⟨225, 225, 18056⟩,
  ⟨229, 229, 18056⟩,
  ⟨233, 233, 18056⟩,
  ⟨237, 237, 18056⟩,
  ⟨257, 129, 14472⟩,
  ⟨261, 137, 14472⟩,
  ⟨265, 133, 14472⟩,
  ⟨269, 141, 14472⟩,
  ⟨289, 193, 14472⟩,
  ⟨293, 201, 14472⟩,
  ⟨297, 197, 14472⟩,
  ⟨301, 205, 14472⟩,
  ⟨321, 161, 14472⟩,
  ⟨325, 169, 14472⟩,
  ⟨329, 165, 14472⟩,
  ⟨333, 173, 14472⟩,
  ⟨353, 225, 14472⟩,
  ⟨357, 233, 14472⟩,
  ⟨361, 229, 14472⟩,
  ⟨365, 237, 14472⟩,
  ⟨385, 385, 18056⟩,
  ⟨389, 389, 18056⟩,
  ⟨393, 389, 14472⟩,
  ⟨397, 397, 18056⟩,
  ⟨417, 417, 18056⟩,
  ⟨421, 421, 18056⟩,
  ⟨425, 425, 18056⟩,
  ⟨429, 429, 18056⟩,
  ⟨449, 417, 14472⟩,
  ⟨453, 425, 14472⟩,
  ⟨457, 421, 14472⟩,
  ⟨461, 429, 14472⟩,
  ⟨481, 481, 18056⟩,
  ⟨485, 485, 18056⟩,
  ⟨489, 485, 14472⟩,
  ⟨493, 493, 18056⟩,
  ⟨513, 513, 18056⟩,
  ⟨517, 517, 18056⟩,
  ⟨521, 517, 14472⟩,
  ⟨525, 525, 18056⟩,
  ⟨545, 545, 18056⟩,
  ⟨549, 549, 18056⟩,
  ⟨553, 553, 18056⟩,
  ⟨557, 557, 18056⟩,
  ⟨577, 545, 14472⟩,
  ⟨581, 553, 14472⟩,
  ⟨585, 549, 14472⟩,
  ⟨589, 557, 14472⟩,
  ⟨609, 609, 18056⟩,
  ⟨613, 613, 18056⟩,
  ⟨617, 613, 14472⟩,
  ⟨621, 621, 18056⟩,
  ⟨641, 641, 18056⟩,
  ⟨645, 645, 18056⟩,
  ⟨649, 649, 18056⟩,
  ⟨653, 653, 18056⟩,
  ⟨673, 673, 18056⟩,
  ⟨677, 677, 18056⟩,
  ⟨681, 681, 18056⟩,
  ⟨685, 685, 18056⟩,
  ⟨705, 705, 18056⟩,
  ⟨709, 709, 18056⟩,
  ⟨713, 713, 18056⟩,
  ⟨717, 717, 18056⟩,
  ⟨737, 737, 18056⟩,
  ⟨741, 741, 18056⟩,
  ⟨745, 745, 18056⟩,
  ⟨749, 749, 18056⟩,
  ⟨769, 641, 14472⟩,
  ⟨773, 649, 14472⟩,
  ⟨777, 645, 14472⟩,
  ⟨781, 653, 14472⟩,
  ⟨801, 705, 14472⟩,
  ⟨805, 713, 14472⟩,
  ⟨809, 709, 14472⟩,
  ⟨813, 717, 14472⟩,
  ⟨833, 673, 14472⟩,
  ⟨837, 681, 14472⟩,
  ⟨841, 677, 14472⟩,
  ⟨845, 685, 14472⟩,
  ⟨865, 737, 14472⟩,
  ⟨869, 745, 14472⟩,
  ⟨873, 741, 14472⟩,
  ⟨877, 749, 14472⟩,
  ⟨897, 897, 18056⟩,
  ⟨901, 901, 18056⟩,
  ⟨905, 901, 14472⟩,
  ⟨909, 909, 18056⟩,
  ⟨929, 929, 18056⟩,
  ⟨933, 933, 18056⟩,
  ⟨937, 937, 18056⟩,
  ⟨941, 941, 18056⟩,
  ⟨961, 929, 14472⟩,
  ⟨965, 937, 14472⟩,
  ⟨969, 933, 14472⟩,
  ⟨973, 941, 14472⟩,
  ⟨993, 993, 18056⟩,
  ⟨997, 997, 18056⟩,
  ⟨1001, 997, 14472⟩,
  ⟨1005, 1005, 18056⟩
]

theorem flag_sources_edge_isolate :
    flagWitnesses_edge_isolate.map RootedFlagWitness.source =
      (List.range (2 ^ 10)).filter (fun m => rootTypeCheck 3 1 (maskGraph 5 m)) := by
  decide +kernel

theorem flag_witnesses_edge_isolate_checked :
    flagWitnesses_edge_isolate.all (rootedFlagRowCheck 5 3 flagBasis_edge_isolate) = true := by
  decide +kernel

theorem flag_basis_edge_isolate_certificate :
    flagBasis_edge_isolate = (Generated.certificate.blocks[2]!).masks.toList := by
  decide +kernel

theorem flag_basis_edge_isolate_count : flagBasis_edge_isolate.length = 72 := by decide +kernel

theorem flag_basis_edge_isolate_nodup : flagBasis_edge_isolate.Nodup := by decide +kernel

theorem flag_basis_edge_isolate_types_checked :
    flagBasis_edge_isolate.all (fun m => rootTypeCheck 3 1 (maskGraph 5 m)) = true := by
  decide +kernel

theorem flag_basis_edge_isolate_covers :
    RootedFlagBasisCovers 5 3 1 flagBasis_edge_isolate :=
  rootedFlagBasisCovers_of_rows edgeIndexSeparated_five
    edgeIndexBounded_five flagBasis_edge_isolate flagWitnesses_edge_isolate
    flag_sources_edge_isolate flag_witnesses_edge_isolate_checked

theorem certificate_flag_basis_edge_isolate_covers :
    RootedFlagBasisCovers 5 3 1
      (Generated.certificate.blocks[2]!).masks.toList := by
  rw [← flag_basis_edge_isolate_certificate]
  exact flag_basis_edge_isolate_covers

end InducedPentagons.Paper

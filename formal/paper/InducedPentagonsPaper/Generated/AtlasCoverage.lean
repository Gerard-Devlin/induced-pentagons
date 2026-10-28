import InducedPentagonsPaper.Generated.AtlasChecksSmall
import InducedPentagonsPaper.Generated.AtlasChecks5_00
import InducedPentagonsPaper.Generated.AtlasChecks5_01
import InducedPentagonsPaper.Generated.AtlasChecks5_02
import InducedPentagonsPaper.Generated.AtlasChecks5_03
import InducedPentagonsPaper.Generated.AtlasChecks6_00
import InducedPentagonsPaper.Generated.AtlasChecks6_01
import InducedPentagonsPaper.Generated.AtlasChecks6_02
import InducedPentagonsPaper.Generated.AtlasChecks6_03
import InducedPentagonsPaper.Generated.AtlasChecks6_04
import InducedPentagonsPaper.Generated.AtlasChecks6_05
import InducedPentagonsPaper.Generated.AtlasChecks6_06
import InducedPentagonsPaper.Generated.AtlasChecks6_07
import InducedPentagonsPaper.Generated.AtlasChecks6_08
import InducedPentagonsPaper.Generated.AtlasChecks6_09
import InducedPentagonsPaper.Generated.AtlasChecks6_10
import InducedPentagonsPaper.Generated.AtlasChecks6_11
import InducedPentagonsPaper.Generated.AtlasChecks6_12
import InducedPentagonsPaper.Generated.AtlasChecks6_13
import InducedPentagonsPaper.Generated.AtlasChecks6_14
import InducedPentagonsPaper.Generated.AtlasChecks6_15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace InducedPentagons.Paper

theorem atlasRows0_sources : atlasRows0.map AtlasRow.source = atlasMasks0 := by
  decide +kernel

theorem atlasRows1_sources : atlasRows1.map AtlasRow.source = atlasMasks1 := by
  decide +kernel

theorem atlasRows2_sources : atlasRows2.map AtlasRow.source = atlasMasks2 := by
  decide +kernel

theorem atlasRows3_sources : atlasRows3.map AtlasRow.source = atlasMasks3 := by
  decide +kernel

theorem atlasRows4_sources : atlasRows4.map AtlasRow.source = atlasMasks4 := by
  decide +kernel

theorem atlasRows5_sources : atlasRows5.map AtlasRow.source = atlasMasks5 := by
  decide +kernel

theorem atlasRows5_checked :
    atlasRows5.all (atlasRowCheck 5 atlasMasks6) = true := by
  simp only [atlasRows5, List.all_cons, List.all_nil,
    atlasRow5_000_checked, atlasRow5_001_checked, atlasRow5_002_checked, atlasRow5_003_checked, atlasRow5_004_checked,
    atlasRow5_005_checked, atlasRow5_006_checked, atlasRow5_007_checked, atlasRow5_008_checked, atlasRow5_009_checked,
    atlasRow5_010_checked, atlasRow5_011_checked, atlasRow5_012_checked, atlasRow5_013_checked, atlasRow5_014_checked,
    atlasRow5_015_checked, atlasRow5_016_checked, atlasRow5_017_checked, atlasRow5_018_checked, atlasRow5_019_checked,
    atlasRow5_020_checked, atlasRow5_021_checked, atlasRow5_022_checked, atlasRow5_023_checked, atlasRow5_024_checked,
    atlasRow5_025_checked, atlasRow5_026_checked, atlasRow5_027_checked, atlasRow5_028_checked, atlasRow5_029_checked,
    atlasRow5_030_checked, atlasRow5_031_checked, atlasRow5_032_checked, atlasRow5_033_checked, Bool.and_self]

theorem atlasRows6_sources : atlasRows6.map AtlasRow.source = atlasMasks6 := by
  decide +kernel

theorem atlasRows6_checked :
    atlasRows6.all (atlasRowCheck 6 atlasMasks7) = true := by
  simp only [atlasRows6, List.all_cons, List.all_nil,
    atlasRow6_000_checked, atlasRow6_001_checked, atlasRow6_002_checked, atlasRow6_003_checked, atlasRow6_004_checked,
    atlasRow6_005_checked, atlasRow6_006_checked, atlasRow6_007_checked, atlasRow6_008_checked, atlasRow6_009_checked,
    atlasRow6_010_checked, atlasRow6_011_checked, atlasRow6_012_checked, atlasRow6_013_checked, atlasRow6_014_checked,
    atlasRow6_015_checked, atlasRow6_016_checked, atlasRow6_017_checked, atlasRow6_018_checked, atlasRow6_019_checked,
    atlasRow6_020_checked, atlasRow6_021_checked, atlasRow6_022_checked, atlasRow6_023_checked, atlasRow6_024_checked,
    atlasRow6_025_checked, atlasRow6_026_checked, atlasRow6_027_checked, atlasRow6_028_checked, atlasRow6_029_checked,
    atlasRow6_030_checked, atlasRow6_031_checked, atlasRow6_032_checked, atlasRow6_033_checked, atlasRow6_034_checked,
    atlasRow6_035_checked, atlasRow6_036_checked, atlasRow6_037_checked, atlasRow6_038_checked, atlasRow6_039_checked,
    atlasRow6_040_checked, atlasRow6_041_checked, atlasRow6_042_checked, atlasRow6_043_checked, atlasRow6_044_checked,
    atlasRow6_045_checked, atlasRow6_046_checked, atlasRow6_047_checked, atlasRow6_048_checked, atlasRow6_049_checked,
    atlasRow6_050_checked, atlasRow6_051_checked, atlasRow6_052_checked, atlasRow6_053_checked, atlasRow6_054_checked,
    atlasRow6_055_checked, atlasRow6_056_checked, atlasRow6_057_checked, atlasRow6_058_checked, atlasRow6_059_checked,
    atlasRow6_060_checked, atlasRow6_061_checked, atlasRow6_062_checked, atlasRow6_063_checked, atlasRow6_064_checked,
    atlasRow6_065_checked, atlasRow6_066_checked, atlasRow6_067_checked, atlasRow6_068_checked, atlasRow6_069_checked,
    atlasRow6_070_checked, atlasRow6_071_checked, atlasRow6_072_checked, atlasRow6_073_checked, atlasRow6_074_checked,
    atlasRow6_075_checked, atlasRow6_076_checked, atlasRow6_077_checked, atlasRow6_078_checked, atlasRow6_079_checked,
    atlasRow6_080_checked, atlasRow6_081_checked, atlasRow6_082_checked, atlasRow6_083_checked, atlasRow6_084_checked,
    atlasRow6_085_checked, atlasRow6_086_checked, atlasRow6_087_checked, atlasRow6_088_checked, atlasRow6_089_checked,
    atlasRow6_090_checked, atlasRow6_091_checked, atlasRow6_092_checked, atlasRow6_093_checked, atlasRow6_094_checked,
    atlasRow6_095_checked, atlasRow6_096_checked, atlasRow6_097_checked, atlasRow6_098_checked, atlasRow6_099_checked,
    atlasRow6_100_checked, atlasRow6_101_checked, atlasRow6_102_checked, atlasRow6_103_checked, atlasRow6_104_checked,
    atlasRow6_105_checked, atlasRow6_106_checked, atlasRow6_107_checked, atlasRow6_108_checked, atlasRow6_109_checked,
    atlasRow6_110_checked, atlasRow6_111_checked, atlasRow6_112_checked, atlasRow6_113_checked, atlasRow6_114_checked,
    atlasRow6_115_checked, atlasRow6_116_checked, atlasRow6_117_checked, atlasRow6_118_checked, atlasRow6_119_checked,
    atlasRow6_120_checked, atlasRow6_121_checked, atlasRow6_122_checked, atlasRow6_123_checked, atlasRow6_124_checked,
    atlasRow6_125_checked, atlasRow6_126_checked, atlasRow6_127_checked, atlasRow6_128_checked, atlasRow6_129_checked,
    atlasRow6_130_checked, atlasRow6_131_checked, atlasRow6_132_checked, atlasRow6_133_checked, atlasRow6_134_checked,
    atlasRow6_135_checked, atlasRow6_136_checked, atlasRow6_137_checked, atlasRow6_138_checked, atlasRow6_139_checked,
    atlasRow6_140_checked, atlasRow6_141_checked, atlasRow6_142_checked, atlasRow6_143_checked, atlasRow6_144_checked,
    atlasRow6_145_checked, atlasRow6_146_checked, atlasRow6_147_checked, atlasRow6_148_checked, atlasRow6_149_checked,
    atlasRow6_150_checked, atlasRow6_151_checked, atlasRow6_152_checked, atlasRow6_153_checked, atlasRow6_154_checked,
    atlasRow6_155_checked, Bool.and_self]

theorem atlas0_covers : AtlasCovers 0 atlasMasks0 := atlasCovers_zero

theorem atlas1_covers : AtlasCovers 1 atlasMasks1 :=
  atlasCovers_succ atlas0_covers
    (atlasExtends_of_rows (by decide) atlasRows0 atlasRows0_sources atlasRows0_checked)

theorem atlas2_covers : AtlasCovers 2 atlasMasks2 :=
  atlasCovers_succ atlas1_covers
    (atlasExtends_of_rows (by decide) atlasRows1 atlasRows1_sources atlasRows1_checked)

theorem atlas3_covers : AtlasCovers 3 atlasMasks3 :=
  atlasCovers_succ atlas2_covers
    (atlasExtends_of_rows (by decide) atlasRows2 atlasRows2_sources atlasRows2_checked)

theorem atlas4_covers : AtlasCovers 4 atlasMasks4 :=
  atlasCovers_succ atlas3_covers
    (atlasExtends_of_rows (by decide) atlasRows3 atlasRows3_sources atlasRows3_checked)

theorem atlas5_covers : AtlasCovers 5 atlasMasks5 :=
  atlasCovers_succ atlas4_covers
    (atlasExtends_of_rows (by decide) atlasRows4 atlasRows4_sources atlasRows4_checked)

theorem atlas6_covers : AtlasCovers 6 atlasMasks6 :=
  atlasCovers_succ atlas5_covers
    (atlasExtends_of_rows (by decide) atlasRows5 atlasRows5_sources atlasRows5_checked)

theorem atlas7_covers : AtlasCovers 7 atlasMasks7 :=
  atlasCovers_succ atlas6_covers
    (atlasExtends_of_rows (by decide) atlasRows6 atlasRows6_sources atlasRows6_checked)

theorem atlas7_count : atlasMasks7.length = 1044 := by decide +kernel

theorem atlas7_masks_nodup : atlasMasks7.Nodup := by decide +kernel

theorem seven_vertex_graph_isomorphic_to_atlas (g : Graph (Fin 7)) :
    ∃ m ∈ atlasMasks7, Nonempty (toSimpleGraph g ≃g toSimpleGraph (maskGraph 7 m)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := atlas7_covers g
  exact ⟨m, hm, ⟨e.toSimpleGraphIso⟩⟩

end InducedPentagons.Paper

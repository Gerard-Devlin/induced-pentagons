import InducedPentagonsPaper.Generated.FixedRows079
import InducedPentagonsPaper.Generated.FixedRows080
import InducedPentagonsPaper.Generated.FixedRows081
import InducedPentagonsPaper.Generated.FixedRows082
import InducedPentagonsPaper.Generated.FixedRows083
import InducedPentagonsPaper.Generated.FixedRows084
import InducedPentagonsPaper.Generated.FixedRows085
import InducedPentagonsPaper.Generated.FixedRows086
import InducedPentagonsPaper.Generated.PrimitiveComplete

namespace InducedPentagons.Paper

set_option maxRecDepth 100000 in
theorem fixed_certificate_rows_semantics :
    ∀ h ∈ primitiveCertificateRows, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  simp only [primitiveCertificateRows, List.mem_append, or_assoc] at hh
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86
  · exact fixed_chunk_000_semantics h h0
  · exact fixed_chunk_001_semantics h h1
  · exact fixed_chunk_002_semantics h h2
  · exact fixed_chunk_003_semantics h h3
  · exact fixed_chunk_004_semantics h h4
  · exact fixed_chunk_005_semantics h h5
  · exact fixed_chunk_006_semantics h h6
  · exact fixed_chunk_007_semantics h h7
  · exact fixed_chunk_008_semantics h h8
  · exact fixed_chunk_009_semantics h h9
  · exact fixed_chunk_010_semantics h h10
  · exact fixed_chunk_011_semantics h h11
  · exact fixed_chunk_012_semantics h h12
  · exact fixed_chunk_013_semantics h h13
  · exact fixed_chunk_014_semantics h h14
  · exact fixed_chunk_015_semantics h h15
  · exact fixed_chunk_016_semantics h h16
  · exact fixed_chunk_017_semantics h h17
  · exact fixed_chunk_018_semantics h h18
  · exact fixed_chunk_019_semantics h h19
  · exact fixed_chunk_020_semantics h h20
  · exact fixed_chunk_021_semantics h h21
  · exact fixed_chunk_022_semantics h h22
  · exact fixed_chunk_023_semantics h h23
  · exact fixed_chunk_024_semantics h h24
  · exact fixed_chunk_025_semantics h h25
  · exact fixed_chunk_026_semantics h h26
  · exact fixed_chunk_027_semantics h h27
  · exact fixed_chunk_028_semantics h h28
  · exact fixed_chunk_029_semantics h h29
  · exact fixed_chunk_030_semantics h h30
  · exact fixed_chunk_031_semantics h h31
  · exact fixed_chunk_032_semantics h h32
  · exact fixed_chunk_033_semantics h h33
  · exact fixed_chunk_034_semantics h h34
  · exact fixed_chunk_035_semantics h h35
  · exact fixed_chunk_036_semantics h h36
  · exact fixed_chunk_037_semantics h h37
  · exact fixed_chunk_038_semantics h h38
  · exact fixed_chunk_039_semantics h h39
  · exact fixed_chunk_040_semantics h h40
  · exact fixed_chunk_041_semantics h h41
  · exact fixed_chunk_042_semantics h h42
  · exact fixed_chunk_043_semantics h h43
  · exact fixed_chunk_044_semantics h h44
  · exact fixed_chunk_045_semantics h h45
  · exact fixed_chunk_046_semantics h h46
  · exact fixed_chunk_047_semantics h h47
  · exact fixed_chunk_048_semantics h h48
  · exact fixed_chunk_049_semantics h h49
  · exact fixed_chunk_050_semantics h h50
  · exact fixed_chunk_051_semantics h h51
  · exact fixed_chunk_052_semantics h h52
  · exact fixed_chunk_053_semantics h h53
  · exact fixed_chunk_054_semantics h h54
  · exact fixed_chunk_055_semantics h h55
  · exact fixed_chunk_056_semantics h h56
  · exact fixed_chunk_057_semantics h h57
  · exact fixed_chunk_058_semantics h h58
  · exact fixed_chunk_059_semantics h h59
  · exact fixed_chunk_060_semantics h h60
  · exact fixed_chunk_061_semantics h h61
  · exact fixed_chunk_062_semantics h h62
  · exact fixed_chunk_063_semantics h h63
  · exact fixed_chunk_064_semantics h h64
  · exact fixed_chunk_065_semantics h h65
  · exact fixed_chunk_066_semantics h h66
  · exact fixed_chunk_067_semantics h h67
  · exact fixed_chunk_068_semantics h h68
  · exact fixed_chunk_069_semantics h h69
  · exact fixed_chunk_070_semantics h h70
  · exact fixed_chunk_071_semantics h h71
  · exact fixed_chunk_072_semantics h h72
  · exact fixed_chunk_073_semantics h h73
  · exact fixed_chunk_074_semantics h h74
  · exact fixed_chunk_075_semantics h h75
  · exact fixed_chunk_076_semantics h h76
  · exact fixed_chunk_077_semantics h h77
  · exact fixed_chunk_078_semantics h h78
  · exact fixed_chunk_079_semantics h h79
  · exact fixed_chunk_080_semantics h h80
  · exact fixed_chunk_081_semantics h h81
  · exact fixed_chunk_082_semantics h h82
  · exact fixed_chunk_083_semantics h h83
  · exact fixed_chunk_084_semantics h h84
  · exact fixed_chunk_085_semantics h h85
  · exact fixed_chunk_086_semantics h h86

end InducedPentagons.Paper

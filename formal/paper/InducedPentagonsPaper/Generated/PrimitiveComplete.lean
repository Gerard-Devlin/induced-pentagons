import InducedPentagonsPaper.Generated.PrimitiveRows079
import InducedPentagonsPaper.Generated.PrimitiveRows080
import InducedPentagonsPaper.Generated.PrimitiveRows081
import InducedPentagonsPaper.Generated.PrimitiveRows082
import InducedPentagonsPaper.Generated.PrimitiveRows083
import InducedPentagonsPaper.Generated.PrimitiveRows084
import InducedPentagonsPaper.Generated.PrimitiveRows085
import InducedPentagonsPaper.Generated.PrimitiveRows086

namespace InducedPentagons.Paper

def primitiveCertificateRows : List HostRow :=
  Generated.hostChunk000.toList ++
  Generated.hostChunk001.toList ++
  Generated.hostChunk002.toList ++
  Generated.hostChunk003.toList ++
  Generated.hostChunk004.toList ++
  Generated.hostChunk005.toList ++
  Generated.hostChunk006.toList ++
  Generated.hostChunk007.toList ++
  Generated.hostChunk008.toList ++
  Generated.hostChunk009.toList ++
  Generated.hostChunk010.toList ++
  Generated.hostChunk011.toList ++
  Generated.hostChunk012.toList ++
  Generated.hostChunk013.toList ++
  Generated.hostChunk014.toList ++
  Generated.hostChunk015.toList ++
  Generated.hostChunk016.toList ++
  Generated.hostChunk017.toList ++
  Generated.hostChunk018.toList ++
  Generated.hostChunk019.toList ++
  Generated.hostChunk020.toList ++
  Generated.hostChunk021.toList ++
  Generated.hostChunk022.toList ++
  Generated.hostChunk023.toList ++
  Generated.hostChunk024.toList ++
  Generated.hostChunk025.toList ++
  Generated.hostChunk026.toList ++
  Generated.hostChunk027.toList ++
  Generated.hostChunk028.toList ++
  Generated.hostChunk029.toList ++
  Generated.hostChunk030.toList ++
  Generated.hostChunk031.toList ++
  Generated.hostChunk032.toList ++
  Generated.hostChunk033.toList ++
  Generated.hostChunk034.toList ++
  Generated.hostChunk035.toList ++
  Generated.hostChunk036.toList ++
  Generated.hostChunk037.toList ++
  Generated.hostChunk038.toList ++
  Generated.hostChunk039.toList ++
  Generated.hostChunk040.toList ++
  Generated.hostChunk041.toList ++
  Generated.hostChunk042.toList ++
  Generated.hostChunk043.toList ++
  Generated.hostChunk044.toList ++
  Generated.hostChunk045.toList ++
  Generated.hostChunk046.toList ++
  Generated.hostChunk047.toList ++
  Generated.hostChunk048.toList ++
  Generated.hostChunk049.toList ++
  Generated.hostChunk050.toList ++
  Generated.hostChunk051.toList ++
  Generated.hostChunk052.toList ++
  Generated.hostChunk053.toList ++
  Generated.hostChunk054.toList ++
  Generated.hostChunk055.toList ++
  Generated.hostChunk056.toList ++
  Generated.hostChunk057.toList ++
  Generated.hostChunk058.toList ++
  Generated.hostChunk059.toList ++
  Generated.hostChunk060.toList ++
  Generated.hostChunk061.toList ++
  Generated.hostChunk062.toList ++
  Generated.hostChunk063.toList ++
  Generated.hostChunk064.toList ++
  Generated.hostChunk065.toList ++
  Generated.hostChunk066.toList ++
  Generated.hostChunk067.toList ++
  Generated.hostChunk068.toList ++
  Generated.hostChunk069.toList ++
  Generated.hostChunk070.toList ++
  Generated.hostChunk071.toList ++
  Generated.hostChunk072.toList ++
  Generated.hostChunk073.toList ++
  Generated.hostChunk074.toList ++
  Generated.hostChunk075.toList ++
  Generated.hostChunk076.toList ++
  Generated.hostChunk077.toList ++
  Generated.hostChunk078.toList ++
  Generated.hostChunk079.toList ++
  Generated.hostChunk080.toList ++
  Generated.hostChunk081.toList ++
  Generated.hostChunk082.toList ++
  Generated.hostChunk083.toList ++
  Generated.hostChunk084.toList ++
  Generated.hostChunk085.toList ++
  Generated.hostChunk086.toList

set_option maxRecDepth 100000 in
theorem primitive_certificate_rows_semantics :
    ∀ h ∈ primitiveCertificateRows, h.primitive.toList =
      primitiveSemanticCounts primitivePatternSpecs (maskGraph 7 h.mask) := by
  intro h hh
  simp only [primitiveCertificateRows, List.mem_append, or_assoc] at hh
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86
  · exact primitive_chunk_000_semantics h h0
  · exact primitive_chunk_001_semantics h h1
  · exact primitive_chunk_002_semantics h h2
  · exact primitive_chunk_003_semantics h h3
  · exact primitive_chunk_004_semantics h h4
  · exact primitive_chunk_005_semantics h h5
  · exact primitive_chunk_006_semantics h h6
  · exact primitive_chunk_007_semantics h h7
  · exact primitive_chunk_008_semantics h h8
  · exact primitive_chunk_009_semantics h h9
  · exact primitive_chunk_010_semantics h h10
  · exact primitive_chunk_011_semantics h h11
  · exact primitive_chunk_012_semantics h h12
  · exact primitive_chunk_013_semantics h h13
  · exact primitive_chunk_014_semantics h h14
  · exact primitive_chunk_015_semantics h h15
  · exact primitive_chunk_016_semantics h h16
  · exact primitive_chunk_017_semantics h h17
  · exact primitive_chunk_018_semantics h h18
  · exact primitive_chunk_019_semantics h h19
  · exact primitive_chunk_020_semantics h h20
  · exact primitive_chunk_021_semantics h h21
  · exact primitive_chunk_022_semantics h h22
  · exact primitive_chunk_023_semantics h h23
  · exact primitive_chunk_024_semantics h h24
  · exact primitive_chunk_025_semantics h h25
  · exact primitive_chunk_026_semantics h h26
  · exact primitive_chunk_027_semantics h h27
  · exact primitive_chunk_028_semantics h h28
  · exact primitive_chunk_029_semantics h h29
  · exact primitive_chunk_030_semantics h h30
  · exact primitive_chunk_031_semantics h h31
  · exact primitive_chunk_032_semantics h h32
  · exact primitive_chunk_033_semantics h h33
  · exact primitive_chunk_034_semantics h h34
  · exact primitive_chunk_035_semantics h h35
  · exact primitive_chunk_036_semantics h h36
  · exact primitive_chunk_037_semantics h h37
  · exact primitive_chunk_038_semantics h h38
  · exact primitive_chunk_039_semantics h h39
  · exact primitive_chunk_040_semantics h h40
  · exact primitive_chunk_041_semantics h h41
  · exact primitive_chunk_042_semantics h h42
  · exact primitive_chunk_043_semantics h h43
  · exact primitive_chunk_044_semantics h h44
  · exact primitive_chunk_045_semantics h h45
  · exact primitive_chunk_046_semantics h h46
  · exact primitive_chunk_047_semantics h h47
  · exact primitive_chunk_048_semantics h h48
  · exact primitive_chunk_049_semantics h h49
  · exact primitive_chunk_050_semantics h h50
  · exact primitive_chunk_051_semantics h h51
  · exact primitive_chunk_052_semantics h h52
  · exact primitive_chunk_053_semantics h h53
  · exact primitive_chunk_054_semantics h h54
  · exact primitive_chunk_055_semantics h h55
  · exact primitive_chunk_056_semantics h h56
  · exact primitive_chunk_057_semantics h h57
  · exact primitive_chunk_058_semantics h h58
  · exact primitive_chunk_059_semantics h h59
  · exact primitive_chunk_060_semantics h h60
  · exact primitive_chunk_061_semantics h h61
  · exact primitive_chunk_062_semantics h h62
  · exact primitive_chunk_063_semantics h h63
  · exact primitive_chunk_064_semantics h h64
  · exact primitive_chunk_065_semantics h h65
  · exact primitive_chunk_066_semantics h h66
  · exact primitive_chunk_067_semantics h h67
  · exact primitive_chunk_068_semantics h h68
  · exact primitive_chunk_069_semantics h h69
  · exact primitive_chunk_070_semantics h h70
  · exact primitive_chunk_071_semantics h h71
  · exact primitive_chunk_072_semantics h h72
  · exact primitive_chunk_073_semantics h h73
  · exact primitive_chunk_074_semantics h h74
  · exact primitive_chunk_075_semantics h h75
  · exact primitive_chunk_076_semantics h h76
  · exact primitive_chunk_077_semantics h h77
  · exact primitive_chunk_078_semantics h h78
  · exact primitive_chunk_079_semantics h h79
  · exact primitive_chunk_080_semantics h h80
  · exact primitive_chunk_081_semantics h h81
  · exact primitive_chunk_082_semantics h h82
  · exact primitive_chunk_083_semantics h h83
  · exact primitive_chunk_084_semantics h h84
  · exact primitive_chunk_085_semantics h h85
  · exact primitive_chunk_086_semantics h h86

end InducedPentagons.Paper

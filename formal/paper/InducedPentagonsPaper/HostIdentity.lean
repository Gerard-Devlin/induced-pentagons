import InducedPentagonsPaper.PrimitiveCertificate
import InducedPentagons.Generated.Complete

/-! The checked integer identities hold on every stored host, with transfer
of the primitive part to every seven-vertex graph. -/

namespace InducedPentagons.Paper

theorem checkHost_identity {c : Certificate} {g : GramData} {h : HostRow}
    (hc : checkHost c g h = true) : hostLeft c h = hostRight c g h := by
  simpa only [beq_iff_eq] using (Bool.and_eq_true_iff.mp hc).2

theorem checkHostChunk_identity {c : Certificate} {g : GramData} {start : Nat}
    {rows : Array HostRow} (hc : checkHostChunk c g start rows = true)
    (h : HostRow) (hh : h ∈ rows.toList) : hostLeft c h = hostRight c g h := by
  have hall := (Bool.and_eq_true_iff.mp hc).2
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hh
  have hi' : i < rows.size := by simpa only [Array.length_toList] using hi
  have hcheck := List.all_eq_true.mp hall i (List.mem_range.mpr hi')
  have hhost := (Bool.and_eq_true_iff.mp hcheck).2
  have he' : rows[i]! = h := by
    rw [getElem!_pos rows i hi']
    simpa only [Array.getElem_toList] using he
  rw [he'] at hhost
  exact checkHost_identity hhost

set_option maxRecDepth 100000 in
theorem certificate_host_identities :
    ∀ h ∈ primitiveCertificateRows,
      hostLeft Generated.certificate h = hostRight Generated.certificate Generated.gramData h := by
  intro h hh
  simp only [primitiveCertificateRows, List.mem_append, or_assoc] at hh
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86
  · exact checkHostChunk_identity Generated.hosts_000_checked h h0
  · exact checkHostChunk_identity Generated.hosts_001_checked h h1
  · exact checkHostChunk_identity Generated.hosts_002_checked h h2
  · exact checkHostChunk_identity Generated.hosts_003_checked h h3
  · exact checkHostChunk_identity Generated.hosts_004_checked h h4
  · exact checkHostChunk_identity Generated.hosts_005_checked h h5
  · exact checkHostChunk_identity Generated.hosts_006_checked h h6
  · exact checkHostChunk_identity Generated.hosts_007_checked h h7
  · exact checkHostChunk_identity Generated.hosts_008_checked h h8
  · exact checkHostChunk_identity Generated.hosts_009_checked h h9
  · exact checkHostChunk_identity Generated.hosts_010_checked h h10
  · exact checkHostChunk_identity Generated.hosts_011_checked h h11
  · exact checkHostChunk_identity Generated.hosts_012_checked h h12
  · exact checkHostChunk_identity Generated.hosts_013_checked h h13
  · exact checkHostChunk_identity Generated.hosts_014_checked h h14
  · exact checkHostChunk_identity Generated.hosts_015_checked h h15
  · exact checkHostChunk_identity Generated.hosts_016_checked h h16
  · exact checkHostChunk_identity Generated.hosts_017_checked h h17
  · exact checkHostChunk_identity Generated.hosts_018_checked h h18
  · exact checkHostChunk_identity Generated.hosts_019_checked h h19
  · exact checkHostChunk_identity Generated.hosts_020_checked h h20
  · exact checkHostChunk_identity Generated.hosts_021_checked h h21
  · exact checkHostChunk_identity Generated.hosts_022_checked h h22
  · exact checkHostChunk_identity Generated.hosts_023_checked h h23
  · exact checkHostChunk_identity Generated.hosts_024_checked h h24
  · exact checkHostChunk_identity Generated.hosts_025_checked h h25
  · exact checkHostChunk_identity Generated.hosts_026_checked h h26
  · exact checkHostChunk_identity Generated.hosts_027_checked h h27
  · exact checkHostChunk_identity Generated.hosts_028_checked h h28
  · exact checkHostChunk_identity Generated.hosts_029_checked h h29
  · exact checkHostChunk_identity Generated.hosts_030_checked h h30
  · exact checkHostChunk_identity Generated.hosts_031_checked h h31
  · exact checkHostChunk_identity Generated.hosts_032_checked h h32
  · exact checkHostChunk_identity Generated.hosts_033_checked h h33
  · exact checkHostChunk_identity Generated.hosts_034_checked h h34
  · exact checkHostChunk_identity Generated.hosts_035_checked h h35
  · exact checkHostChunk_identity Generated.hosts_036_checked h h36
  · exact checkHostChunk_identity Generated.hosts_037_checked h h37
  · exact checkHostChunk_identity Generated.hosts_038_checked h h38
  · exact checkHostChunk_identity Generated.hosts_039_checked h h39
  · exact checkHostChunk_identity Generated.hosts_040_checked h h40
  · exact checkHostChunk_identity Generated.hosts_041_checked h h41
  · exact checkHostChunk_identity Generated.hosts_042_checked h h42
  · exact checkHostChunk_identity Generated.hosts_043_checked h h43
  · exact checkHostChunk_identity Generated.hosts_044_checked h h44
  · exact checkHostChunk_identity Generated.hosts_045_checked h h45
  · exact checkHostChunk_identity Generated.hosts_046_checked h h46
  · exact checkHostChunk_identity Generated.hosts_047_checked h h47
  · exact checkHostChunk_identity Generated.hosts_048_checked h h48
  · exact checkHostChunk_identity Generated.hosts_049_checked h h49
  · exact checkHostChunk_identity Generated.hosts_050_checked h h50
  · exact checkHostChunk_identity Generated.hosts_051_checked h h51
  · exact checkHostChunk_identity Generated.hosts_052_checked h h52
  · exact checkHostChunk_identity Generated.hosts_053_checked h h53
  · exact checkHostChunk_identity Generated.hosts_054_checked h h54
  · exact checkHostChunk_identity Generated.hosts_055_checked h h55
  · exact checkHostChunk_identity Generated.hosts_056_checked h h56
  · exact checkHostChunk_identity Generated.hosts_057_checked h h57
  · exact checkHostChunk_identity Generated.hosts_058_checked h h58
  · exact checkHostChunk_identity Generated.hosts_059_checked h h59
  · exact checkHostChunk_identity Generated.hosts_060_checked h h60
  · exact checkHostChunk_identity Generated.hosts_061_checked h h61
  · exact checkHostChunk_identity Generated.hosts_062_checked h h62
  · exact checkHostChunk_identity Generated.hosts_063_checked h h63
  · exact checkHostChunk_identity Generated.hosts_064_checked h h64
  · exact checkHostChunk_identity Generated.hosts_065_checked h h65
  · exact checkHostChunk_identity Generated.hosts_066_checked h h66
  · exact checkHostChunk_identity Generated.hosts_067_checked h h67
  · exact checkHostChunk_identity Generated.hosts_068_checked h h68
  · exact checkHostChunk_identity Generated.hosts_069_checked h h69
  · exact checkHostChunk_identity Generated.hosts_070_checked h h70
  · exact checkHostChunk_identity Generated.hosts_071_checked h h71
  · exact checkHostChunk_identity Generated.hosts_072_checked h h72
  · exact checkHostChunk_identity Generated.hosts_073_checked h h73
  · exact checkHostChunk_identity Generated.hosts_074_checked h h74
  · exact checkHostChunk_identity Generated.hosts_075_checked h h75
  · exact checkHostChunk_identity Generated.hosts_076_checked h h76
  · exact checkHostChunk_identity Generated.hosts_077_checked h h77
  · exact checkHostChunk_identity Generated.hosts_078_checked h h78
  · exact checkHostChunk_identity Generated.hosts_079_checked h h79
  · exact checkHostChunk_identity Generated.hosts_080_checked h h80
  · exact checkHostChunk_identity Generated.hosts_081_checked h h81
  · exact checkHostChunk_identity Generated.hosts_082_checked h h82
  · exact checkHostChunk_identity Generated.hosts_083_checked h h83
  · exact checkHostChunk_identity Generated.hosts_084_checked h h84
  · exact checkHostChunk_identity Generated.hosts_085_checked h h85
  · exact checkHostChunk_identity Generated.hosts_086_checked h h86

/-- Every seven-vertex graph has a certificate representative whose exact
integer identity and primitive sampling interpretation are both proved. -/
theorem host_identity_on_all_seven_vertex_graphs (g : Graph (Fin 7)) :
    ∃ h ∈ primitiveCertificateRows, Nonempty (BooleanGraphEquiv g (maskGraph 7 h.mask)) ∧
      primitiveSemanticCounts primitivePatternSpecs g = h.primitive.toList ∧
      hostLeft Generated.certificate h = hostRight Generated.certificate Generated.gramData h := by
  obtain ⟨h, hh, he, hp⟩ := primitive_counts_on_all_seven_vertex_graphs g
  exact ⟨h, hh, he, hp, certificate_host_identities h hh⟩

end InducedPentagons.Paper



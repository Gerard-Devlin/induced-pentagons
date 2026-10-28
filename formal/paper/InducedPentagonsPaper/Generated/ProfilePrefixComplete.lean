module
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks00
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks01
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks02
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks03
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks04
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks05
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks06
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks07
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks08
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks09
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks10
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks11
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks12
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks13
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks14
public import InducedPentagonsPaper.Generated.ProfilePrefixChecks15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] public section
namespace InducedPentagons.Paper

theorem clebsch_profile_boolean_bound (b : Fin 16 → Bool) :
    patternTotal maskLiteral clebschProfileMasks b ≤ 60 := by
  rw [← patternTotal_filter_all maskLiteral clebschProfileMasks b profilePrefixVars]
  change patternTotal maskLiteral (clebschProfileMasks.filter
    (fun p => acceptLiteral (maskLiteral p 0) (b 0) && (acceptLiteral (maskLiteral p 1) (b 1) && (acceptLiteral (maskLiteral p 2) (b 2) && (acceptLiteral (maskLiteral p 3) (b 3) && (acceptLiteral (maskLiteral p 4) (b 4) && (acceptLiteral (maskLiteral p 5) (b 5) && (acceptLiteral (maskLiteral p 6) (b 6) && (acceptLiteral (maskLiteral p 7) (b 7) && (true)))))))))) b ≤ 60
  cases h0 : b 0 with
  | false =>
    cases h1 : b 1 with
    | false =>
      cases h2 : b 2 with
      | false =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 0) b ≤ 60
                  rw [profilePrefixData000]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks000 profilePrefixChecked000 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 128) b ≤ 60
                  rw [profilePrefixData128]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks128 profilePrefixChecked128 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 64) b ≤ 60
                  rw [profilePrefixData064]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks064 profilePrefixChecked064 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 192) b ≤ 60
                  rw [profilePrefixData192]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks192 profilePrefixChecked192 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 32) b ≤ 60
                  rw [profilePrefixData032]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks032 profilePrefixChecked032 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 160) b ≤ 60
                  rw [profilePrefixData160]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks160 profilePrefixChecked160 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 96) b ≤ 60
                  rw [profilePrefixData096]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks096 profilePrefixChecked096 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 224) b ≤ 60
                  rw [profilePrefixData224]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks224 profilePrefixChecked224 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 16) b ≤ 60
                  rw [profilePrefixData016]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks016 profilePrefixChecked016 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 144) b ≤ 60
                  rw [profilePrefixData144]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks144 profilePrefixChecked144 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 80) b ≤ 60
                  rw [profilePrefixData080]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks080 profilePrefixChecked080 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 208) b ≤ 60
                  rw [profilePrefixData208]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks208 profilePrefixChecked208 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 48) b ≤ 60
                  rw [profilePrefixData048]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks048 profilePrefixChecked048 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 176) b ≤ 60
                  rw [profilePrefixData176]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks176 profilePrefixChecked176 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 112) b ≤ 60
                  rw [profilePrefixData112]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks112 profilePrefixChecked112 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 240) b ≤ 60
                  rw [profilePrefixData240]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks240 profilePrefixChecked240 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 8) b ≤ 60
                  rw [profilePrefixData008]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks008 profilePrefixChecked008 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 136) b ≤ 60
                  rw [profilePrefixData136]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks136 profilePrefixChecked136 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 72) b ≤ 60
                  rw [profilePrefixData072]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks072 profilePrefixChecked072 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 200) b ≤ 60
                  rw [profilePrefixData200]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks200 profilePrefixChecked200 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 40) b ≤ 60
                  rw [profilePrefixData040]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks040 profilePrefixChecked040 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 168) b ≤ 60
                  rw [profilePrefixData168]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks168 profilePrefixChecked168 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 104) b ≤ 60
                  rw [profilePrefixData104]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks104 profilePrefixChecked104 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 232) b ≤ 60
                  rw [profilePrefixData232]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks232 profilePrefixChecked232 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 24) b ≤ 60
                  rw [profilePrefixData024]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks024 profilePrefixChecked024 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 152) b ≤ 60
                  rw [profilePrefixData152]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks152 profilePrefixChecked152 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 88) b ≤ 60
                  rw [profilePrefixData088]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks088 profilePrefixChecked088 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 216) b ≤ 60
                  rw [profilePrefixData216]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks216 profilePrefixChecked216 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 56) b ≤ 60
                  rw [profilePrefixData056]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks056 profilePrefixChecked056 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 184) b ≤ 60
                  rw [profilePrefixData184]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks184 profilePrefixChecked184 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 120) b ≤ 60
                  rw [profilePrefixData120]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks120 profilePrefixChecked120 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 248) b ≤ 60
                  rw [profilePrefixData248]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks248 profilePrefixChecked248 b
      | true =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 4) b ≤ 60
                  rw [profilePrefixData004]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks004 profilePrefixChecked004 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 132) b ≤ 60
                  rw [profilePrefixData132]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks132 profilePrefixChecked132 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 68) b ≤ 60
                  rw [profilePrefixData068]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks068 profilePrefixChecked068 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 196) b ≤ 60
                  rw [profilePrefixData196]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks196 profilePrefixChecked196 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 36) b ≤ 60
                  rw [profilePrefixData036]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks036 profilePrefixChecked036 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 164) b ≤ 60
                  rw [profilePrefixData164]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks164 profilePrefixChecked164 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 100) b ≤ 60
                  rw [profilePrefixData100]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks100 profilePrefixChecked100 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 228) b ≤ 60
                  rw [profilePrefixData228]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks228 profilePrefixChecked228 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 20) b ≤ 60
                  rw [profilePrefixData020]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks020 profilePrefixChecked020 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 148) b ≤ 60
                  rw [profilePrefixData148]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks148 profilePrefixChecked148 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 84) b ≤ 60
                  rw [profilePrefixData084]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks084 profilePrefixChecked084 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 212) b ≤ 60
                  rw [profilePrefixData212]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks212 profilePrefixChecked212 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 52) b ≤ 60
                  rw [profilePrefixData052]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks052 profilePrefixChecked052 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 180) b ≤ 60
                  rw [profilePrefixData180]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks180 profilePrefixChecked180 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 116) b ≤ 60
                  rw [profilePrefixData116]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks116 profilePrefixChecked116 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 244) b ≤ 60
                  rw [profilePrefixData244]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks244 profilePrefixChecked244 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 12) b ≤ 60
                  rw [profilePrefixData012]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks012 profilePrefixChecked012 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 140) b ≤ 60
                  rw [profilePrefixData140]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks140 profilePrefixChecked140 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 76) b ≤ 60
                  rw [profilePrefixData076]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks076 profilePrefixChecked076 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 204) b ≤ 60
                  rw [profilePrefixData204]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks204 profilePrefixChecked204 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 44) b ≤ 60
                  rw [profilePrefixData044]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks044 profilePrefixChecked044 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 172) b ≤ 60
                  rw [profilePrefixData172]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks172 profilePrefixChecked172 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 108) b ≤ 60
                  rw [profilePrefixData108]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks108 profilePrefixChecked108 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 236) b ≤ 60
                  rw [profilePrefixData236]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks236 profilePrefixChecked236 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 28) b ≤ 60
                  rw [profilePrefixData028]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks028 profilePrefixChecked028 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 156) b ≤ 60
                  rw [profilePrefixData156]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks156 profilePrefixChecked156 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 92) b ≤ 60
                  rw [profilePrefixData092]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks092 profilePrefixChecked092 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 220) b ≤ 60
                  rw [profilePrefixData220]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks220 profilePrefixChecked220 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 60) b ≤ 60
                  rw [profilePrefixData060]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks060 profilePrefixChecked060 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 188) b ≤ 60
                  rw [profilePrefixData188]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks188 profilePrefixChecked188 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 124) b ≤ 60
                  rw [profilePrefixData124]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks124 profilePrefixChecked124 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 252) b ≤ 60
                  rw [profilePrefixData252]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks252 profilePrefixChecked252 b
    | true =>
      cases h2 : b 2 with
      | false =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 2) b ≤ 60
                  rw [profilePrefixData002]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks002 profilePrefixChecked002 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 130) b ≤ 60
                  rw [profilePrefixData130]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks130 profilePrefixChecked130 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 66) b ≤ 60
                  rw [profilePrefixData066]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks066 profilePrefixChecked066 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 194) b ≤ 60
                  rw [profilePrefixData194]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks194 profilePrefixChecked194 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 34) b ≤ 60
                  rw [profilePrefixData034]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks034 profilePrefixChecked034 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 162) b ≤ 60
                  rw [profilePrefixData162]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks162 profilePrefixChecked162 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 98) b ≤ 60
                  rw [profilePrefixData098]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks098 profilePrefixChecked098 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 226) b ≤ 60
                  rw [profilePrefixData226]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks226 profilePrefixChecked226 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 18) b ≤ 60
                  rw [profilePrefixData018]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks018 profilePrefixChecked018 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 146) b ≤ 60
                  rw [profilePrefixData146]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks146 profilePrefixChecked146 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 82) b ≤ 60
                  rw [profilePrefixData082]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks082 profilePrefixChecked082 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 210) b ≤ 60
                  rw [profilePrefixData210]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks210 profilePrefixChecked210 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 50) b ≤ 60
                  rw [profilePrefixData050]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks050 profilePrefixChecked050 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 178) b ≤ 60
                  rw [profilePrefixData178]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks178 profilePrefixChecked178 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 114) b ≤ 60
                  rw [profilePrefixData114]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks114 profilePrefixChecked114 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 242) b ≤ 60
                  rw [profilePrefixData242]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks242 profilePrefixChecked242 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 10) b ≤ 60
                  rw [profilePrefixData010]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks010 profilePrefixChecked010 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 138) b ≤ 60
                  rw [profilePrefixData138]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks138 profilePrefixChecked138 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 74) b ≤ 60
                  rw [profilePrefixData074]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks074 profilePrefixChecked074 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 202) b ≤ 60
                  rw [profilePrefixData202]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks202 profilePrefixChecked202 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 42) b ≤ 60
                  rw [profilePrefixData042]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks042 profilePrefixChecked042 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 170) b ≤ 60
                  rw [profilePrefixData170]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks170 profilePrefixChecked170 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 106) b ≤ 60
                  rw [profilePrefixData106]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks106 profilePrefixChecked106 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 234) b ≤ 60
                  rw [profilePrefixData234]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks234 profilePrefixChecked234 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 26) b ≤ 60
                  rw [profilePrefixData026]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks026 profilePrefixChecked026 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 154) b ≤ 60
                  rw [profilePrefixData154]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks154 profilePrefixChecked154 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 90) b ≤ 60
                  rw [profilePrefixData090]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks090 profilePrefixChecked090 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 218) b ≤ 60
                  rw [profilePrefixData218]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks218 profilePrefixChecked218 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 58) b ≤ 60
                  rw [profilePrefixData058]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks058 profilePrefixChecked058 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 186) b ≤ 60
                  rw [profilePrefixData186]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks186 profilePrefixChecked186 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 122) b ≤ 60
                  rw [profilePrefixData122]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks122 profilePrefixChecked122 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 250) b ≤ 60
                  rw [profilePrefixData250]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks250 profilePrefixChecked250 b
      | true =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 6) b ≤ 60
                  rw [profilePrefixData006]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks006 profilePrefixChecked006 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 134) b ≤ 60
                  rw [profilePrefixData134]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks134 profilePrefixChecked134 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 70) b ≤ 60
                  rw [profilePrefixData070]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks070 profilePrefixChecked070 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 198) b ≤ 60
                  rw [profilePrefixData198]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks198 profilePrefixChecked198 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 38) b ≤ 60
                  rw [profilePrefixData038]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks038 profilePrefixChecked038 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 166) b ≤ 60
                  rw [profilePrefixData166]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks166 profilePrefixChecked166 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 102) b ≤ 60
                  rw [profilePrefixData102]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks102 profilePrefixChecked102 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 230) b ≤ 60
                  rw [profilePrefixData230]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks230 profilePrefixChecked230 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 22) b ≤ 60
                  rw [profilePrefixData022]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks022 profilePrefixChecked022 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 150) b ≤ 60
                  rw [profilePrefixData150]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks150 profilePrefixChecked150 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 86) b ≤ 60
                  rw [profilePrefixData086]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks086 profilePrefixChecked086 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 214) b ≤ 60
                  rw [profilePrefixData214]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks214 profilePrefixChecked214 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 54) b ≤ 60
                  rw [profilePrefixData054]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks054 profilePrefixChecked054 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 182) b ≤ 60
                  rw [profilePrefixData182]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks182 profilePrefixChecked182 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 118) b ≤ 60
                  rw [profilePrefixData118]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks118 profilePrefixChecked118 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 246) b ≤ 60
                  rw [profilePrefixData246]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks246 profilePrefixChecked246 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 14) b ≤ 60
                  rw [profilePrefixData014]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks014 profilePrefixChecked014 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 142) b ≤ 60
                  rw [profilePrefixData142]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks142 profilePrefixChecked142 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 78) b ≤ 60
                  rw [profilePrefixData078]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks078 profilePrefixChecked078 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 206) b ≤ 60
                  rw [profilePrefixData206]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks206 profilePrefixChecked206 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 46) b ≤ 60
                  rw [profilePrefixData046]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks046 profilePrefixChecked046 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 174) b ≤ 60
                  rw [profilePrefixData174]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks174 profilePrefixChecked174 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 110) b ≤ 60
                  rw [profilePrefixData110]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks110 profilePrefixChecked110 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 238) b ≤ 60
                  rw [profilePrefixData238]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks238 profilePrefixChecked238 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 30) b ≤ 60
                  rw [profilePrefixData030]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks030 profilePrefixChecked030 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 158) b ≤ 60
                  rw [profilePrefixData158]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks158 profilePrefixChecked158 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 94) b ≤ 60
                  rw [profilePrefixData094]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks094 profilePrefixChecked094 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 222) b ≤ 60
                  rw [profilePrefixData222]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks222 profilePrefixChecked222 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 62) b ≤ 60
                  rw [profilePrefixData062]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks062 profilePrefixChecked062 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 190) b ≤ 60
                  rw [profilePrefixData190]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks190 profilePrefixChecked190 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 126) b ≤ 60
                  rw [profilePrefixData126]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks126 profilePrefixChecked126 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 254) b ≤ 60
                  rw [profilePrefixData254]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks254 profilePrefixChecked254 b
  | true =>
    cases h1 : b 1 with
    | false =>
      cases h2 : b 2 with
      | false =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 1) b ≤ 60
                  rw [profilePrefixData001]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks001 profilePrefixChecked001 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 129) b ≤ 60
                  rw [profilePrefixData129]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks129 profilePrefixChecked129 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 65) b ≤ 60
                  rw [profilePrefixData065]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks065 profilePrefixChecked065 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 193) b ≤ 60
                  rw [profilePrefixData193]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks193 profilePrefixChecked193 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 33) b ≤ 60
                  rw [profilePrefixData033]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks033 profilePrefixChecked033 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 161) b ≤ 60
                  rw [profilePrefixData161]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks161 profilePrefixChecked161 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 97) b ≤ 60
                  rw [profilePrefixData097]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks097 profilePrefixChecked097 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 225) b ≤ 60
                  rw [profilePrefixData225]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks225 profilePrefixChecked225 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 17) b ≤ 60
                  rw [profilePrefixData017]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks017 profilePrefixChecked017 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 145) b ≤ 60
                  rw [profilePrefixData145]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks145 profilePrefixChecked145 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 81) b ≤ 60
                  rw [profilePrefixData081]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks081 profilePrefixChecked081 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 209) b ≤ 60
                  rw [profilePrefixData209]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks209 profilePrefixChecked209 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 49) b ≤ 60
                  rw [profilePrefixData049]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks049 profilePrefixChecked049 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 177) b ≤ 60
                  rw [profilePrefixData177]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks177 profilePrefixChecked177 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 113) b ≤ 60
                  rw [profilePrefixData113]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks113 profilePrefixChecked113 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 241) b ≤ 60
                  rw [profilePrefixData241]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks241 profilePrefixChecked241 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 9) b ≤ 60
                  rw [profilePrefixData009]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks009 profilePrefixChecked009 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 137) b ≤ 60
                  rw [profilePrefixData137]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks137 profilePrefixChecked137 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 73) b ≤ 60
                  rw [profilePrefixData073]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks073 profilePrefixChecked073 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 201) b ≤ 60
                  rw [profilePrefixData201]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks201 profilePrefixChecked201 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 41) b ≤ 60
                  rw [profilePrefixData041]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks041 profilePrefixChecked041 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 169) b ≤ 60
                  rw [profilePrefixData169]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks169 profilePrefixChecked169 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 105) b ≤ 60
                  rw [profilePrefixData105]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks105 profilePrefixChecked105 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 233) b ≤ 60
                  rw [profilePrefixData233]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks233 profilePrefixChecked233 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 25) b ≤ 60
                  rw [profilePrefixData025]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks025 profilePrefixChecked025 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 153) b ≤ 60
                  rw [profilePrefixData153]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks153 profilePrefixChecked153 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 89) b ≤ 60
                  rw [profilePrefixData089]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks089 profilePrefixChecked089 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 217) b ≤ 60
                  rw [profilePrefixData217]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks217 profilePrefixChecked217 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 57) b ≤ 60
                  rw [profilePrefixData057]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks057 profilePrefixChecked057 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 185) b ≤ 60
                  rw [profilePrefixData185]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks185 profilePrefixChecked185 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 121) b ≤ 60
                  rw [profilePrefixData121]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks121 profilePrefixChecked121 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 249) b ≤ 60
                  rw [profilePrefixData249]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks249 profilePrefixChecked249 b
      | true =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 5) b ≤ 60
                  rw [profilePrefixData005]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks005 profilePrefixChecked005 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 133) b ≤ 60
                  rw [profilePrefixData133]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks133 profilePrefixChecked133 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 69) b ≤ 60
                  rw [profilePrefixData069]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks069 profilePrefixChecked069 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 197) b ≤ 60
                  rw [profilePrefixData197]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks197 profilePrefixChecked197 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 37) b ≤ 60
                  rw [profilePrefixData037]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks037 profilePrefixChecked037 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 165) b ≤ 60
                  rw [profilePrefixData165]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks165 profilePrefixChecked165 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 101) b ≤ 60
                  rw [profilePrefixData101]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks101 profilePrefixChecked101 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 229) b ≤ 60
                  rw [profilePrefixData229]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks229 profilePrefixChecked229 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 21) b ≤ 60
                  rw [profilePrefixData021]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks021 profilePrefixChecked021 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 149) b ≤ 60
                  rw [profilePrefixData149]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks149 profilePrefixChecked149 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 85) b ≤ 60
                  rw [profilePrefixData085]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks085 profilePrefixChecked085 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 213) b ≤ 60
                  rw [profilePrefixData213]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks213 profilePrefixChecked213 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 53) b ≤ 60
                  rw [profilePrefixData053]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks053 profilePrefixChecked053 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 181) b ≤ 60
                  rw [profilePrefixData181]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks181 profilePrefixChecked181 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 117) b ≤ 60
                  rw [profilePrefixData117]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks117 profilePrefixChecked117 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 245) b ≤ 60
                  rw [profilePrefixData245]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks245 profilePrefixChecked245 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 13) b ≤ 60
                  rw [profilePrefixData013]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks013 profilePrefixChecked013 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 141) b ≤ 60
                  rw [profilePrefixData141]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks141 profilePrefixChecked141 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 77) b ≤ 60
                  rw [profilePrefixData077]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks077 profilePrefixChecked077 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 205) b ≤ 60
                  rw [profilePrefixData205]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks205 profilePrefixChecked205 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 45) b ≤ 60
                  rw [profilePrefixData045]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks045 profilePrefixChecked045 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 173) b ≤ 60
                  rw [profilePrefixData173]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks173 profilePrefixChecked173 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 109) b ≤ 60
                  rw [profilePrefixData109]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks109 profilePrefixChecked109 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 237) b ≤ 60
                  rw [profilePrefixData237]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks237 profilePrefixChecked237 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 29) b ≤ 60
                  rw [profilePrefixData029]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks029 profilePrefixChecked029 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 157) b ≤ 60
                  rw [profilePrefixData157]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks157 profilePrefixChecked157 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 93) b ≤ 60
                  rw [profilePrefixData093]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks093 profilePrefixChecked093 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 221) b ≤ 60
                  rw [profilePrefixData221]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks221 profilePrefixChecked221 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 61) b ≤ 60
                  rw [profilePrefixData061]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks061 profilePrefixChecked061 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 189) b ≤ 60
                  rw [profilePrefixData189]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks189 profilePrefixChecked189 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 125) b ≤ 60
                  rw [profilePrefixData125]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks125 profilePrefixChecked125 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 253) b ≤ 60
                  rw [profilePrefixData253]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks253 profilePrefixChecked253 b
    | true =>
      cases h2 : b 2 with
      | false =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 3) b ≤ 60
                  rw [profilePrefixData003]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks003 profilePrefixChecked003 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 131) b ≤ 60
                  rw [profilePrefixData131]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks131 profilePrefixChecked131 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 67) b ≤ 60
                  rw [profilePrefixData067]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks067 profilePrefixChecked067 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 195) b ≤ 60
                  rw [profilePrefixData195]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks195 profilePrefixChecked195 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 35) b ≤ 60
                  rw [profilePrefixData035]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks035 profilePrefixChecked035 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 163) b ≤ 60
                  rw [profilePrefixData163]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks163 profilePrefixChecked163 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 99) b ≤ 60
                  rw [profilePrefixData099]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks099 profilePrefixChecked099 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 227) b ≤ 60
                  rw [profilePrefixData227]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks227 profilePrefixChecked227 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 19) b ≤ 60
                  rw [profilePrefixData019]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks019 profilePrefixChecked019 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 147) b ≤ 60
                  rw [profilePrefixData147]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks147 profilePrefixChecked147 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 83) b ≤ 60
                  rw [profilePrefixData083]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks083 profilePrefixChecked083 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 211) b ≤ 60
                  rw [profilePrefixData211]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks211 profilePrefixChecked211 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 51) b ≤ 60
                  rw [profilePrefixData051]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks051 profilePrefixChecked051 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 179) b ≤ 60
                  rw [profilePrefixData179]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks179 profilePrefixChecked179 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 115) b ≤ 60
                  rw [profilePrefixData115]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks115 profilePrefixChecked115 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 243) b ≤ 60
                  rw [profilePrefixData243]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks243 profilePrefixChecked243 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 11) b ≤ 60
                  rw [profilePrefixData011]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks011 profilePrefixChecked011 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 139) b ≤ 60
                  rw [profilePrefixData139]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks139 profilePrefixChecked139 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 75) b ≤ 60
                  rw [profilePrefixData075]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks075 profilePrefixChecked075 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 203) b ≤ 60
                  rw [profilePrefixData203]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks203 profilePrefixChecked203 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 43) b ≤ 60
                  rw [profilePrefixData043]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks043 profilePrefixChecked043 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 171) b ≤ 60
                  rw [profilePrefixData171]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks171 profilePrefixChecked171 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 107) b ≤ 60
                  rw [profilePrefixData107]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks107 profilePrefixChecked107 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 235) b ≤ 60
                  rw [profilePrefixData235]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks235 profilePrefixChecked235 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 27) b ≤ 60
                  rw [profilePrefixData027]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks027 profilePrefixChecked027 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 155) b ≤ 60
                  rw [profilePrefixData155]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks155 profilePrefixChecked155 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 91) b ≤ 60
                  rw [profilePrefixData091]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks091 profilePrefixChecked091 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 219) b ≤ 60
                  rw [profilePrefixData219]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks219 profilePrefixChecked219 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 59) b ≤ 60
                  rw [profilePrefixData059]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks059 profilePrefixChecked059 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 187) b ≤ 60
                  rw [profilePrefixData187]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks187 profilePrefixChecked187 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 123) b ≤ 60
                  rw [profilePrefixData123]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks123 profilePrefixChecked123 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 251) b ≤ 60
                  rw [profilePrefixData251]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks251 profilePrefixChecked251 b
      | true =>
        cases h3 : b 3 with
        | false =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 7) b ≤ 60
                  rw [profilePrefixData007]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks007 profilePrefixChecked007 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 135) b ≤ 60
                  rw [profilePrefixData135]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks135 profilePrefixChecked135 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 71) b ≤ 60
                  rw [profilePrefixData071]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks071 profilePrefixChecked071 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 199) b ≤ 60
                  rw [profilePrefixData199]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks199 profilePrefixChecked199 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 39) b ≤ 60
                  rw [profilePrefixData039]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks039 profilePrefixChecked039 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 167) b ≤ 60
                  rw [profilePrefixData167]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks167 profilePrefixChecked167 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 103) b ≤ 60
                  rw [profilePrefixData103]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks103 profilePrefixChecked103 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 231) b ≤ 60
                  rw [profilePrefixData231]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks231 profilePrefixChecked231 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 23) b ≤ 60
                  rw [profilePrefixData023]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks023 profilePrefixChecked023 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 151) b ≤ 60
                  rw [profilePrefixData151]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks151 profilePrefixChecked151 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 87) b ≤ 60
                  rw [profilePrefixData087]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks087 profilePrefixChecked087 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 215) b ≤ 60
                  rw [profilePrefixData215]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks215 profilePrefixChecked215 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 55) b ≤ 60
                  rw [profilePrefixData055]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks055 profilePrefixChecked055 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 183) b ≤ 60
                  rw [profilePrefixData183]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks183 profilePrefixChecked183 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 119) b ≤ 60
                  rw [profilePrefixData119]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks119 profilePrefixChecked119 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 247) b ≤ 60
                  rw [profilePrefixData247]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks247 profilePrefixChecked247 b
        | true =>
          cases h4 : b 4 with
          | false =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 15) b ≤ 60
                  rw [profilePrefixData015]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks015 profilePrefixChecked015 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 143) b ≤ 60
                  rw [profilePrefixData143]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks143 profilePrefixChecked143 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 79) b ≤ 60
                  rw [profilePrefixData079]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks079 profilePrefixChecked079 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 207) b ≤ 60
                  rw [profilePrefixData207]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks207 profilePrefixChecked207 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 47) b ≤ 60
                  rw [profilePrefixData047]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks047 profilePrefixChecked047 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 175) b ≤ 60
                  rw [profilePrefixData175]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks175 profilePrefixChecked175 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 111) b ≤ 60
                  rw [profilePrefixData111]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks111 profilePrefixChecked111 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 239) b ≤ 60
                  rw [profilePrefixData239]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks239 profilePrefixChecked239 b
          | true =>
            cases h5 : b 5 with
            | false =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 31) b ≤ 60
                  rw [profilePrefixData031]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks031 profilePrefixChecked031 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 159) b ≤ 60
                  rw [profilePrefixData159]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks159 profilePrefixChecked159 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 95) b ≤ 60
                  rw [profilePrefixData095]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks095 profilePrefixChecked095 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 223) b ≤ 60
                  rw [profilePrefixData223]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks223 profilePrefixChecked223 b
            | true =>
              cases h6 : b 6 with
              | false =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 63) b ≤ 60
                  rw [profilePrefixData063]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks063 profilePrefixChecked063 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 191) b ≤ 60
                  rw [profilePrefixData191]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks191 profilePrefixChecked191 b
              | true =>
                cases h7 : b 7 with
                | false =>
                  change patternTotal maskLiteral (profilePrefixFamily 127) b ≤ 60
                  rw [profilePrefixData127]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks127 profilePrefixChecked127 b
                | true =>
                  change patternTotal maskLiteral (profilePrefixFamily 255) b ≤ 60
                  rw [profilePrefixData255]
                  exact patternBound_sound maskLiteral 60 profileRemainingVars profilePrefixMasks255 profilePrefixChecked255 b

end InducedPentagons.Paper

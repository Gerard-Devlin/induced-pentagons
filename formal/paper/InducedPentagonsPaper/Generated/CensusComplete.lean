import InducedPentagonsPaper.Generated.CensusRows00
import InducedPentagonsPaper.Generated.CensusRows01
import InducedPentagonsPaper.Generated.CensusRows02
import InducedPentagonsPaper.Generated.CensusRows03
import InducedPentagonsPaper.Generated.CensusRows04
import InducedPentagonsPaper.Generated.CensusRows05
import InducedPentagonsPaper.Generated.CensusRows06
import InducedPentagonsPaper.Generated.CensusRows07
import InducedPentagonsPaper.Generated.CensusRows08
import InducedPentagonsPaper.Generated.CensusRows09
import InducedPentagonsPaper.Generated.CensusRows10
import InducedPentagonsPaper.Generated.CensusRows11
import InducedPentagonsPaper.Generated.CensusRows12
import InducedPentagonsPaper.Generated.CensusRows13
import InducedPentagonsPaper.Generated.CensusRows14
import InducedPentagonsPaper.Generated.CensusRows15
import InducedPentagonsPaper.Generated.CensusRows16
import InducedPentagonsPaper.Generated.CensusRows17
import InducedPentagonsPaper.Generated.CensusRows18
import InducedPentagonsPaper.Generated.CensusRows19
import InducedPentagonsPaper.Generated.CensusRows20
import InducedPentagonsPaper.Generated.CensusRows21
import InducedPentagonsPaper.Generated.CensusRows22
import InducedPentagonsPaper.Generated.CensusRows23
import InducedPentagonsPaper.Generated.CensusRows24
import InducedPentagonsPaper.Generated.CensusRows25
import InducedPentagonsPaper.Generated.CensusRows26
import InducedPentagonsPaper.Generated.CensusRows27
import InducedPentagonsPaper.Generated.CensusRows28
import InducedPentagonsPaper.Generated.CensusRows29
import InducedPentagonsPaper.Generated.CensusRows30
import InducedPentagonsPaper.Generated.CensusRows31
import InducedPentagonsPaper.Generated.CensusRows32
import InducedPentagonsPaper.Generated.CensusRows33
import InducedPentagonsPaper.Generated.CensusRows34
import InducedPentagonsPaper.Generated.CensusRows35
import InducedPentagonsPaper.Generated.CensusRows36
import InducedPentagonsPaper.Generated.CensusRows37
import InducedPentagonsPaper.Generated.CensusRows38
import InducedPentagonsPaper.Generated.CensusRows39
import InducedPentagonsPaper.Generated.CensusRows40
import InducedPentagonsPaper.Generated.CensusRows41
import InducedPentagonsPaper.Generated.CensusRows42
import InducedPentagonsPaper.Generated.CensusRows43
import InducedPentagonsPaper.AtlasCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

def atlasCensusRows : List AtlasCensusRow :=
  atlasCensusRows00 ++
  atlasCensusRows01 ++
  atlasCensusRows02 ++
  atlasCensusRows03 ++
  atlasCensusRows04 ++
  atlasCensusRows05 ++
  atlasCensusRows06 ++
  atlasCensusRows07 ++
  atlasCensusRows08 ++
  atlasCensusRows09 ++
  atlasCensusRows10 ++
  atlasCensusRows11 ++
  atlasCensusRows12 ++
  atlasCensusRows13 ++
  atlasCensusRows14 ++
  atlasCensusRows15 ++
  atlasCensusRows16 ++
  atlasCensusRows17 ++
  atlasCensusRows18 ++
  atlasCensusRows19 ++
  atlasCensusRows20 ++
  atlasCensusRows21 ++
  atlasCensusRows22 ++
  atlasCensusRows23 ++
  atlasCensusRows24 ++
  atlasCensusRows25 ++
  atlasCensusRows26 ++
  atlasCensusRows27 ++
  atlasCensusRows28 ++
  atlasCensusRows29 ++
  atlasCensusRows30 ++
  atlasCensusRows31 ++
  atlasCensusRows32 ++
  atlasCensusRows33 ++
  atlasCensusRows34 ++
  atlasCensusRows35 ++
  atlasCensusRows36 ++
  atlasCensusRows37 ++
  atlasCensusRows38 ++
  atlasCensusRows39 ++
  atlasCensusRows40 ++
  atlasCensusRows41 ++
  atlasCensusRows42 ++
  atlasCensusRows43

theorem atlas_census_rows_checked : atlasCensusRows.all atlasCensusRowCheck = true := by
  simp only [atlasCensusRows, List.all_append,
    atlasCensusRows00_checked, atlasCensusRows01_checked, atlasCensusRows02_checked, atlasCensusRows03_checked, atlasCensusRows04_checked, atlasCensusRows05_checked, atlasCensusRows06_checked, atlasCensusRows07_checked, atlasCensusRows08_checked, atlasCensusRows09_checked, atlasCensusRows10_checked, atlasCensusRows11_checked, atlasCensusRows12_checked, atlasCensusRows13_checked, atlasCensusRows14_checked, atlasCensusRows15_checked, atlasCensusRows16_checked, atlasCensusRows17_checked, atlasCensusRows18_checked, atlasCensusRows19_checked, atlasCensusRows20_checked, atlasCensusRows21_checked, atlasCensusRows22_checked, atlasCensusRows23_checked, atlasCensusRows24_checked, atlasCensusRows25_checked, atlasCensusRows26_checked, atlasCensusRows27_checked, atlasCensusRows28_checked, atlasCensusRows29_checked, atlasCensusRows30_checked, atlasCensusRows31_checked, atlasCensusRows32_checked, atlasCensusRows33_checked, atlasCensusRows34_checked, atlasCensusRows35_checked, atlasCensusRows36_checked, atlasCensusRows37_checked, atlasCensusRows38_checked, atlasCensusRows39_checked, atlasCensusRows40_checked, atlasCensusRows41_checked, atlasCensusRows42_checked, atlasCensusRows43_checked, Bool.and_self]

theorem atlas_census_hosts : atlasCensusRows.map AtlasCensusRow.mask =
    Generated.certificate.hosts.toList := by decide +kernel

theorem atlas_census_count : atlasCensusRows.length = 1044 := by decide +kernel

theorem atlas_census_semantics (r : AtlasCensusRow) (hr : r ∈ atlasCensusRows) :
    Nat.card (toSimpleGraph (maskGraph 7 r.mask) ≃g
      toSimpleGraph (maskGraph 7 r.mask)) = r.automorphisms ∧
    Nat.card (CensusIsoClass (toSimpleGraph (maskGraph 7 r.mask))) = r.orbit :=
  atlasCensusRowCheck_sound r ((List.all_eq_true.mp atlas_census_rows_checked) r hr)

theorem atlas_census_labelled_total :
    (atlasCensusRows.map AtlasCensusRow.orbit).sum = 2097152 := by decide +kernel

end InducedPentagons.Paper

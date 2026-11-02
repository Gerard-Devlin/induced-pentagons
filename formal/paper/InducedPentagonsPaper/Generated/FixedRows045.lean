import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData045
import InducedPentagonsPaper.Generated.FixedRows037

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0540 :
    (fixedDensityCounts (maskGraph 7 43878), fixedComplementCounts (maskGraph 7 43878)) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 0, 0, 1, 0, 3, 5, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0540_semantics :
    ((Generated.hostChunk045[0]).induced.toList, (Generated.hostChunk045[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[0]).mask)) := by
  have hm : (Generated.hostChunk045[0]).mask = 43878 := by decide +kernel
  have hv : ((Generated.hostChunk045[0]).induced.toList, (Generated.hostChunk045[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 0, 0, 1, 0, 3, 5, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0540]

theorem fixed_values_0541 :
    (fixedDensityCounts (maskGraph 7 43879), fixedComplementCounts (maskGraph 7 43879)) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 2, 0, 1, 0, 0, 4, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0541_semantics :
    ((Generated.hostChunk045[1]).induced.toList, (Generated.hostChunk045[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[1]).mask)) := by
  have hm : (Generated.hostChunk045[1]).mask = 43879 := by decide +kernel
  have hv : ((Generated.hostChunk045[1]).induced.toList, (Generated.hostChunk045[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 2, 0, 1, 0, 0, 4, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0541]

theorem fixed_values_0542 :
    (fixedDensityCounts (maskGraph 7 43884), fixedComplementCounts (maskGraph 7 43884)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 0, 0, 1, 0, 4, 2, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0542_semantics :
    ((Generated.hostChunk045[2]).induced.toList, (Generated.hostChunk045[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[2]).mask)) := by
  have hm : (Generated.hostChunk045[2]).mask = 43884 := by decide +kernel
  have hv : ((Generated.hostChunk045[2]).induced.toList, (Generated.hostChunk045[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 0, 0, 1, 0, 4, 2, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0542]

theorem fixed_values_0543 :
    (fixedDensityCounts (maskGraph 7 43885), fixedComplementCounts (maskGraph 7 43885)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 1, 0, 1, 0, 1, 3, 1, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0543_semantics :
    ((Generated.hostChunk045[3]).induced.toList, (Generated.hostChunk045[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[3]).mask)) := by
  have hm : (Generated.hostChunk045[3]).mask = 43885 := by decide +kernel
  have hv : ((Generated.hostChunk045[3]).induced.toList, (Generated.hostChunk045[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 1, 0, 1, 0, 1, 3, 1, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0543]

theorem fixed_values_0544 :
    (fixedDensityCounts (maskGraph 7 43887), fixedComplementCounts (maskGraph 7 43887)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 2, 0, 1, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0544_semantics :
    ((Generated.hostChunk045[4]).induced.toList, (Generated.hostChunk045[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[4]).mask)) := by
  have hm : (Generated.hostChunk045[4]).mask = 43887 := by decide +kernel
  have hv : ((Generated.hostChunk045[4]).induced.toList, (Generated.hostChunk045[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 2, 0, 1, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0544]

theorem fixed_values_0545 :
    (fixedDensityCounts (maskGraph 7 43888), fixedComplementCounts (maskGraph 7 43888)) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 2, 5, 0, 0, 2, 0, 4, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0545_semantics :
    ((Generated.hostChunk045[5]).induced.toList, (Generated.hostChunk045[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[5]).mask)) := by
  have hm : (Generated.hostChunk045[5]).mask = 43888 := by decide +kernel
  have hv : ((Generated.hostChunk045[5]).induced.toList, (Generated.hostChunk045[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 4, 2, 5, 0, 0, 2, 0, 4, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0545]

theorem fixed_values_0546 :
    (fixedDensityCounts (maskGraph 7 43889), fixedComplementCounts (maskGraph 7 43889)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 3, 2, 1, 0, 1, 0, 4, 1, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0546_semantics :
    ((Generated.hostChunk045[6]).induced.toList, (Generated.hostChunk045[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[6]).mask)) := by
  have hm : (Generated.hostChunk045[6]).mask = 43889 := by decide +kernel
  have hv : ((Generated.hostChunk045[6]).induced.toList, (Generated.hostChunk045[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 3, 2, 1, 0, 1, 0, 4, 1, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0546]

theorem fixed_values_0547 :
    (fixedDensityCounts (maskGraph 7 43891), fixedComplementCounts (maskGraph 7 43891)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 4, 1, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0547_semantics :
    ((Generated.hostChunk045[7]).induced.toList, (Generated.hostChunk045[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[7]).mask)) := by
  have hm : (Generated.hostChunk045[7]).mask = 43891 := by decide +kernel
  have hv : ((Generated.hostChunk045[7]).induced.toList, (Generated.hostChunk045[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 4, 1, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0547]

theorem fixed_values_0548 :
    (fixedDensityCounts (maskGraph 7 43892), fixedComplementCounts (maskGraph 7 43892)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 3, 0, 1, 0, 3, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0548_semantics :
    ((Generated.hostChunk045[8]).induced.toList, (Generated.hostChunk045[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[8]).mask)) := by
  have hm : (Generated.hostChunk045[8]).mask = 43892 := by decide +kernel
  have hv : ((Generated.hostChunk045[8]).induced.toList, (Generated.hostChunk045[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 3, 0, 1, 0, 3, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0548]

theorem fixed_values_0549 :
    (fixedDensityCounts (maskGraph 7 43893), fixedComplementCounts (maskGraph 7 43893)) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 3, 1, 1, 0, 0, 1, 4, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0549_semantics :
    ((Generated.hostChunk045[9]).induced.toList, (Generated.hostChunk045[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[9]).mask)) := by
  have hm : (Generated.hostChunk045[9]).mask = 43893 := by decide +kernel
  have hv : ((Generated.hostChunk045[9]).induced.toList, (Generated.hostChunk045[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 3, 1, 1, 0, 0, 1, 4, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0549]

theorem fixed_values_0550 :
    (fixedDensityCounts (maskGraph 7 43894), fixedComplementCounts (maskGraph 7 43894)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 2, 0, 1, 0, 3, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0550_semantics :
    ((Generated.hostChunk045[10]).induced.toList, (Generated.hostChunk045[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[10]).mask)) := by
  have hm : (Generated.hostChunk045[10]).mask = 43894 := by decide +kernel
  have hv : ((Generated.hostChunk045[10]).induced.toList, (Generated.hostChunk045[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 2, 0, 1, 0, 3, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0550]

theorem fixed_values_0551 :
    (fixedDensityCounts (maskGraph 7 43895), fixedComplementCounts (maskGraph 7 43895)) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 1, 1, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0551_semantics :
    ((Generated.hostChunk045[11]).induced.toList, (Generated.hostChunk045[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk045[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk045[11]).mask)) := by
  have hm : (Generated.hostChunk045[11]).mask = 43895 := by decide +kernel
  have hv : ((Generated.hostChunk045[11]).induced.toList, (Generated.hostChunk045[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 1, 1, 1, 0, 0, 3, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0551]

theorem fixed_chunk_045_semantics :
    ∀ h ∈ Generated.hostChunk045.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk045.toList = [Generated.hostChunk045[0], Generated.hostChunk045[1], Generated.hostChunk045[2], Generated.hostChunk045[3], Generated.hostChunk045[4], Generated.hostChunk045[5], Generated.hostChunk045[6], Generated.hostChunk045[7], Generated.hostChunk045[8], Generated.hostChunk045[9], Generated.hostChunk045[10], Generated.hostChunk045[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0540_semantics
  · exact fixed_host_0541_semantics
  · exact fixed_host_0542_semantics
  · exact fixed_host_0543_semantics
  · exact fixed_host_0544_semantics
  · exact fixed_host_0545_semantics
  · exact fixed_host_0546_semantics
  · exact fixed_host_0547_semantics
  · exact fixed_host_0548_semantics
  · exact fixed_host_0549_semantics
  · exact fixed_host_0550_semantics
  · exact fixed_host_0551_semantics

end InducedPentagons.Paper

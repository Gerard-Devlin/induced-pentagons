import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData079
import InducedPentagonsPaper.Generated.FixedRows071

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0948 :
    (fixedDensityCounts (maskGraph 7 375871), fixedComplementCounts (maskGraph 7 375871)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0948_semantics :
    ((Generated.hostChunk079[0]).induced.toList, (Generated.hostChunk079[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[0]).mask)) := by
  have hm : (Generated.hostChunk079[0]).mask = 375871 := by decide +kernel
  have hv : ((Generated.hostChunk079[0]).induced.toList, (Generated.hostChunk079[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 8, 6, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0948]

theorem fixed_values_0949 :
    (fixedDensityCounts (maskGraph 7 375907), fixedComplementCounts (maskGraph 7 375907)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 6, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0949_semantics :
    ((Generated.hostChunk079[1]).induced.toList, (Generated.hostChunk079[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[1]).mask)) := by
  have hm : (Generated.hostChunk079[1]).mask = 375907 := by decide +kernel
  have hv : ((Generated.hostChunk079[1]).induced.toList, (Generated.hostChunk079[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 6, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0949]

theorem fixed_values_0950 :
    (fixedDensityCounts (maskGraph 7 375909), fixedComplementCounts (maskGraph 7 375909)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 12, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 6, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0950_semantics :
    ((Generated.hostChunk079[2]).induced.toList, (Generated.hostChunk079[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[2]).mask)) := by
  have hm : (Generated.hostChunk079[2]).mask = 375909 := by decide +kernel
  have hv : ((Generated.hostChunk079[2]).induced.toList, (Generated.hostChunk079[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 12, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 6, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0950]

theorem fixed_values_0951 :
    (fixedDensityCounts (maskGraph 7 375911), fixedComplementCounts (maskGraph 7 375911)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 8, 4, 1, 1, 0, 0, 3, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 2, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0951_semantics :
    ((Generated.hostChunk079[3]).induced.toList, (Generated.hostChunk079[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[3]).mask)) := by
  have hm : (Generated.hostChunk079[3]).mask = 375911 := by decide +kernel
  have hv : ((Generated.hostChunk079[3]).induced.toList, (Generated.hostChunk079[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 8, 4, 1, 1, 0, 0, 3, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 2, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0951]

theorem fixed_values_0952 :
    (fixedDensityCounts (maskGraph 7 375917), fixedComplementCounts (maskGraph 7 375917)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 8, 3, 1, 1, 0, 4, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 1, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0952_semantics :
    ((Generated.hostChunk079[4]).induced.toList, (Generated.hostChunk079[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[4]).mask)) := by
  have hm : (Generated.hostChunk079[4]).mask = 375917 := by decide +kernel
  have hv : ((Generated.hostChunk079[4]).induced.toList, (Generated.hostChunk079[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 8, 3, 1, 1, 0, 4, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 1, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0952]

theorem fixed_values_0953 :
    (fixedDensityCounts (maskGraph 7 375919), fixedComplementCounts (maskGraph 7 375919)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 5, 5, 2, 1, 0, 0, 4, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 2, 1, 1, 0, 0, 2, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0953_semantics :
    ((Generated.hostChunk079[5]).induced.toList, (Generated.hostChunk079[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[5]).mask)) := by
  have hm : (Generated.hostChunk079[5]).mask = 375919 := by decide +kernel
  have hv : ((Generated.hostChunk079[5]).induced.toList, (Generated.hostChunk079[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 5, 5, 2, 1, 0, 0, 4, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 2, 1, 1, 0, 0, 2, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0953]

theorem fixed_values_0954 :
    (fixedDensityCounts (maskGraph 7 375932), fixedComplementCounts (maskGraph 7 375932)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 6, 6, 2, 0, 3, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0954_semantics :
    ((Generated.hostChunk079[6]).induced.toList, (Generated.hostChunk079[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[6]).mask)) := by
  have hm : (Generated.hostChunk079[6]).mask = 375932 := by decide +kernel
  have hv : ((Generated.hostChunk079[6]).induced.toList, (Generated.hostChunk079[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 6, 6, 2, 0, 3, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0954]

theorem fixed_values_0955 :
    (fixedDensityCounts (maskGraph 7 375933), fixedComplementCounts (maskGraph 7 375933)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 3, 3, 3, 0, 3, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0]) := by
  decide +kernel

theorem fixed_host_0955_semantics :
    ((Generated.hostChunk079[7]).induced.toList, (Generated.hostChunk079[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[7]).mask)) := by
  have hm : (Generated.hostChunk079[7]).mask = 375933 := by decide +kernel
  have hv : ((Generated.hostChunk079[7]).induced.toList, (Generated.hostChunk079[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 3, 3, 3, 0, 3, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0955]

theorem fixed_values_0956 :
    (fixedDensityCounts (maskGraph 7 375934), fixedComplementCounts (maskGraph 7 375934)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 6, 0, 8, 0, 0, 3, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0956_semantics :
    ((Generated.hostChunk079[8]).induced.toList, (Generated.hostChunk079[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[8]).mask)) := by
  have hm : (Generated.hostChunk079[8]).mask = 375934 := by decide +kernel
  have hv : ((Generated.hostChunk079[8]).induced.toList, (Generated.hostChunk079[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 6, 0, 8, 0, 0, 3, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0956]

theorem fixed_values_0957 :
    (fixedDensityCounts (maskGraph 7 375935), fixedComplementCounts (maskGraph 7 375935)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 6, 3, 0, 0, 3, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 2, 3, 0, 0, 3, 0, 0, 0, 0, 1]) := by
  decide +kernel

theorem fixed_host_0957_semantics :
    ((Generated.hostChunk079[9]).induced.toList, (Generated.hostChunk079[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[9]).mask)) := by
  have hm : (Generated.hostChunk079[9]).mask = 375935 := by decide +kernel
  have hv : ((Generated.hostChunk079[9]).induced.toList, (Generated.hostChunk079[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 6, 3, 0, 0, 3, 0, 3, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 2, 3, 0, 0, 3, 0, 0, 0, 0, 1]) := by decide +kernel
  rw [hm, hv, fixed_values_0957]

theorem fixed_values_0958 :
    (fixedDensityCounts (maskGraph 7 376039), fixedComplementCounts (maskGraph 7 376039)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 8, 0, 2, 0, 0, 0, 0, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0958_semantics :
    ((Generated.hostChunk079[10]).induced.toList, (Generated.hostChunk079[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[10]).mask)) := by
  have hm : (Generated.hostChunk079[10]).mask = 376039 := by decide +kernel
  have hv : ((Generated.hostChunk079[10]).induced.toList, (Generated.hostChunk079[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 8, 0, 2, 0, 0, 0, 0, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 4, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0958]

theorem fixed_values_0959 :
    (fixedDensityCounts (maskGraph 7 376043), fixedComplementCounts (maskGraph 7 376043)) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 5, 0, 0, 0, 2, 4, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 3, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0959_semantics :
    ((Generated.hostChunk079[11]).induced.toList, (Generated.hostChunk079[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk079[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk079[11]).mask)) := by
  have hm : (Generated.hostChunk079[11]).mask = 376043 := by decide +kernel
  have hv : ((Generated.hostChunk079[11]).induced.toList, (Generated.hostChunk079[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 5, 0, 0, 0, 2, 4, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 3, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0959]

theorem fixed_chunk_079_semantics :
    ∀ h ∈ Generated.hostChunk079.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk079.toList = [Generated.hostChunk079[0], Generated.hostChunk079[1], Generated.hostChunk079[2], Generated.hostChunk079[3], Generated.hostChunk079[4], Generated.hostChunk079[5], Generated.hostChunk079[6], Generated.hostChunk079[7], Generated.hostChunk079[8], Generated.hostChunk079[9], Generated.hostChunk079[10], Generated.hostChunk079[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0948_semantics
  · exact fixed_host_0949_semantics
  · exact fixed_host_0950_semantics
  · exact fixed_host_0951_semantics
  · exact fixed_host_0952_semantics
  · exact fixed_host_0953_semantics
  · exact fixed_host_0954_semantics
  · exact fixed_host_0955_semantics
  · exact fixed_host_0956_semantics
  · exact fixed_host_0957_semantics
  · exact fixed_host_0958_semantics
  · exact fixed_host_0959_semantics

end InducedPentagons.Paper

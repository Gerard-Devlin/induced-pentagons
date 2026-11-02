import InducedPentagonsPaper.FixedDensity
import InducedPentagons.Generated.HostData043
import InducedPentagonsPaper.Generated.FixedRows035

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace InducedPentagons.Paper

theorem fixed_values_0516 :
    (fixedDensityCounts (maskGraph 7 42419), fixedComplementCounts (maskGraph 7 42419)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0516_semantics :
    ((Generated.hostChunk043[0]).induced.toList, (Generated.hostChunk043[0]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[0]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[0]).mask)) := by
  have hm : (Generated.hostChunk043[0]).mask = 42419 := by decide +kernel
  have hv : ((Generated.hostChunk043[0]).induced.toList, (Generated.hostChunk043[0]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 4, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0516]

theorem fixed_values_0517 :
    (fixedDensityCounts (maskGraph 7 42422), fixedComplementCounts (maskGraph 7 42422)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0517_semantics :
    ((Generated.hostChunk043[1]).induced.toList, (Generated.hostChunk043[1]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[1]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[1]).mask)) := by
  have hm : (Generated.hostChunk043[1]).mask = 42422 := by decide +kernel
  have hv : ((Generated.hostChunk043[1]).induced.toList, (Generated.hostChunk043[1]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0517]

theorem fixed_values_0518 :
    (fixedDensityCounts (maskGraph 7 42423), fixedComplementCounts (maskGraph 7 42423)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 2, 2, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0518_semantics :
    ((Generated.hostChunk043[2]).induced.toList, (Generated.hostChunk043[2]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[2]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[2]).mask)) := by
  have hm : (Generated.hostChunk043[2]).mask = 42423 := by decide +kernel
  have hv : ((Generated.hostChunk043[2]).induced.toList, (Generated.hostChunk043[2]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 2, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 2, 2, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0518]

theorem fixed_values_0519 :
    (fixedDensityCounts (maskGraph 7 42430), fixedComplementCounts (maskGraph 7 42430)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0519_semantics :
    ((Generated.hostChunk043[3]).induced.toList, (Generated.hostChunk043[3]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[3]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[3]).mask)) := by
  have hm : (Generated.hostChunk043[3]).mask = 42430 := by decide +kernel
  have hv : ((Generated.hostChunk043[3]).induced.toList, (Generated.hostChunk043[3]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 3, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0519]

theorem fixed_values_0520 :
    (fixedDensityCounts (maskGraph 7 42431), fixedComplementCounts (maskGraph 7 42431)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 2, 4, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0520_semantics :
    ((Generated.hostChunk043[4]).induced.toList, (Generated.hostChunk043[4]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[4]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[4]).mask)) := by
  have hm : (Generated.hostChunk043[4]).mask = 42431 := by decide +kernel
  have hv : ((Generated.hostChunk043[4]).induced.toList, (Generated.hostChunk043[4]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 2, 4, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0520]

theorem fixed_values_0521 :
    (fixedDensityCounts (maskGraph 7 42478), fixedComplementCounts (maskGraph 7 42478)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 2, 1, 0, 0, 3, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0521_semantics :
    ((Generated.hostChunk043[5]).induced.toList, (Generated.hostChunk043[5]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[5]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[5]).mask)) := by
  have hm : (Generated.hostChunk043[5]).mask = 42478 := by decide +kernel
  have hv : ((Generated.hostChunk043[5]).induced.toList, (Generated.hostChunk043[5]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 2, 1, 0, 0, 3, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0521]

theorem fixed_values_0522 :
    (fixedDensityCounts (maskGraph 7 42479), fixedComplementCounts (maskGraph 7 42479)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 2, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0522_semantics :
    ((Generated.hostChunk043[6]).induced.toList, (Generated.hostChunk043[6]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[6]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[6]).mask)) := by
  have hm : (Generated.hostChunk043[6]).mask = 42479 := by decide +kernel
  have hv : ((Generated.hostChunk043[6]).induced.toList, (Generated.hostChunk043[6]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 2, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0522]

theorem fixed_values_0523 :
    (fixedDensityCounts (maskGraph 7 42486), fixedComplementCounts (maskGraph 7 42486)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0523_semantics :
    ((Generated.hostChunk043[7]).induced.toList, (Generated.hostChunk043[7]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[7]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[7]).mask)) := by
  have hm : (Generated.hostChunk043[7]).mask = 42486 := by decide +kernel
  have hv : ((Generated.hostChunk043[7]).induced.toList, (Generated.hostChunk043[7]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0523]

theorem fixed_values_0524 :
    (fixedDensityCounts (maskGraph 7 42487), fixedComplementCounts (maskGraph 7 42487)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0524_semantics :
    ((Generated.hostChunk043[8]).induced.toList, (Generated.hostChunk043[8]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[8]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[8]).mask)) := by
  have hm : (Generated.hostChunk043[8]).mask = 42487 := by decide +kernel
  have hv : ((Generated.hostChunk043[8]).induced.toList, (Generated.hostChunk043[8]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0524]

theorem fixed_values_0525 :
    (fixedDensityCounts (maskGraph 7 42492), fixedComplementCounts (maskGraph 7 42492)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0525_semantics :
    ((Generated.hostChunk043[9]).induced.toList, (Generated.hostChunk043[9]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[9]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[9]).mask)) := by
  have hm : (Generated.hostChunk043[9]).mask = 42492 := by decide +kernel
  have hv : ((Generated.hostChunk043[9]).induced.toList, (Generated.hostChunk043[9]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0525]

theorem fixed_values_0526 :
    (fixedDensityCounts (maskGraph 7 42493), fixedComplementCounts (maskGraph 7 42493)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0526_semantics :
    ((Generated.hostChunk043[10]).induced.toList, (Generated.hostChunk043[10]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[10]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[10]).mask)) := by
  have hm : (Generated.hostChunk043[10]).mask = 42493 := by decide +kernel
  have hv : ((Generated.hostChunk043[10]).induced.toList, (Generated.hostChunk043[10]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0526]

theorem fixed_values_0527 :
    (fixedDensityCounts (maskGraph 7 42494), fixedComplementCounts (maskGraph 7 42494)) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 5, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]) := by
  decide +kernel

theorem fixed_host_0527_semantics :
    ((Generated.hostChunk043[11]).induced.toList, (Generated.hostChunk043[11]).complement.toList) =
      (fixedDensityCounts (maskGraph 7 (Generated.hostChunk043[11]).mask), fixedComplementCounts (maskGraph 7 (Generated.hostChunk043[11]).mask)) := by
  have hm : (Generated.hostChunk043[11]).mask = 42494 := by decide +kernel
  have hv : ((Generated.hostChunk043[11]).induced.toList, (Generated.hostChunk043[11]).complement.toList) =
      ([0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 5, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]) := by decide +kernel
  rw [hm, hv, fixed_values_0527]

theorem fixed_chunk_043_semantics :
    ∀ h ∈ Generated.hostChunk043.toList, (h.induced.toList, h.complement.toList) =
      (fixedDensityCounts (maskGraph 7 h.mask), fixedComplementCounts (maskGraph 7 h.mask)) := by
  intro h hh
  have hr : Generated.hostChunk043.toList = [Generated.hostChunk043[0], Generated.hostChunk043[1], Generated.hostChunk043[2], Generated.hostChunk043[3], Generated.hostChunk043[4], Generated.hostChunk043[5], Generated.hostChunk043[6], Generated.hostChunk043[7], Generated.hostChunk043[8], Generated.hostChunk043[9], Generated.hostChunk043[10], Generated.hostChunk043[11]] := rfl
  rw [hr] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixed_host_0516_semantics
  · exact fixed_host_0517_semantics
  · exact fixed_host_0518_semantics
  · exact fixed_host_0519_semantics
  · exact fixed_host_0520_semantics
  · exact fixed_host_0521_semantics
  · exact fixed_host_0522_semantics
  · exact fixed_host_0523_semantics
  · exact fixed_host_0524_semantics
  · exact fixed_host_0525_semantics
  · exact fixed_host_0526_semantics
  · exact fixed_host_0527_semantics

end InducedPentagons.Paper

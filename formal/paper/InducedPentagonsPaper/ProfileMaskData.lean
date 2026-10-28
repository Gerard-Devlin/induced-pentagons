import InducedPentagonsPaper.ProfileData
import InducedPentagonsPaper.Generated.ProfileMasks

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace InducedPentagons.Paper

def pathMask (p : PathTuple 16) : ProfileMask :=
  ⟨2 ^ p.a.val + 2 ^ p.d.val, 2 ^ p.b.val + 2 ^ p.c.val⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profileMaskData_exact :
    clebschProfileMasks = (inducedPaths clebsch).map pathMask := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profileMask_literals_checked :
    (inducedPaths clebsch).all (fun p => (List.finRange 16).all
      (fun i => decide (maskLiteral (pathMask p) i = pathLiteral p i))) = true := by
  decide +kernel

theorem pathMask_literal_eq {p : PathTuple 16} (hp : p ∈ inducedPaths clebsch) :
    maskLiteral (pathMask p) = pathLiteral p := by
  funext i
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp profileMask_literals_checked p hp) i (by simp))

theorem profileLink_mask_sum (x : Fin 16 → ℝ) :
    profileLink x = (clebschProfileMasks.map (fun p => patternValue (maskLiteral p) x)).sum := by
  rw [profileMaskData_exact, List.map_map]
  unfold profileLink
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  change patternValue (pathLiteral p) x = patternValue (maskLiteral (pathMask p)) x
  rw [pathMask_literal_eq hp]

end InducedPentagons.Paper

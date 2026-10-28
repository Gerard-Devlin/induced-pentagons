module
public import InducedPentagonsPaper.MaskPattern
public import InducedPentagonsPaper.Generated.ProfileMasks

@[expose] public section
noncomputable section

namespace InducedPentagons.Paper

theorem patternTotal_filter_all {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (literal : α → ι → Option Bool) (ps : List α) (b : ι → Bool) (vars : List ι) :
    patternTotal literal (ps.filter (fun p => vars.all (fun i => acceptLiteral (literal p i) (b i)))) b =
      patternTotal literal ps b := by
  induction vars generalizing ps with
  | nil => simp
  | cons i rest ih =>
    have hfilter : ps.filter (fun p => (i :: rest).all (fun j => acceptLiteral (literal p j) (b j))) =
        (ps.filter (fun p => acceptLiteral (literal p i) (b i))).filter
          (fun p => rest.all (fun j => acceptLiteral (literal p j) (b j))) := by
      rw [List.filter_filter]
      simp only [List.all_cons]
      congr 1
      funext p
      exact Bool.and_comm _ _
    rw [hfilter, ih, patternTotal_filter]

def profilePrefixVars : List (Fin 16) := (List.finRange 16).take 8

def profileRemainingVars : List (Fin 16) := (List.finRange 16).drop 8

def profilePrefixFamily (bits : Nat) : List ProfileMask :=
  clebschProfileMasks.filter (fun p => profilePrefixVars.all
    (fun i => acceptLiteral (maskLiteral p i) (bits.testBit i.val)))

end InducedPentagons.Paper

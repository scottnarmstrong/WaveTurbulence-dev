/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.MemberUnits
public import WaveTurbulence.Foundations.Vine.A.VineBatchTreeIndex
/-! R-IDX for the literal carried unit regions. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist
variable {w p : ℕ} {kind : Bool} {ι J : Type*} [DecidableEq ι]
  {Q : J → ι → Prop} {L : List ι} {A B : FamilyReconstruction w ι}
  {us : ∀ j, UnitAt A.skeleton A.family (Q j)} {vs : ∀ j, UnitAt B.skeleton B.family (Q j)}

/-- The upper-joint tree index of every carried unit is invariant. -/
theorem member_upper_tree_index (hr : ReachU p kind Q L A us B vs) (hn : L.Nodup) (j : J) :
    (vs j).blk.a.1.1 = (us j).blk.a.1.1 := by
  have h := reachU_coordinates hr hn (batchMolIso_spec hr.batch) j
  exact (congrArg (fun b => b.1.1) h.2.1).trans ((batchMolIso_spec hr.batch).tree_index _)

/-- The leaf profile used by each unit is the common representative profile. -/
theorem member_unitProfile {J : Type} {Q : J → ι → Prop}
    {us : ∀ j, UnitAt A.skeleton A.family (Q j)} {vs : ∀ j, UnitAt B.skeleton B.family (Q j)}
    (hr : ReachU p kind Q L A us B vs) (hn : L.Nodup) {d : ℕ}
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) :
    unitProfile (fun j => unitClBlock (vs j)) f = unitProfile (fun j => unitClBlock (us j)) f := by
  funext j
  unfold unitProfile
  rw [show (unitClBlock (vs j)).upper.1.1 = (unitClBlock (us j)).upper.1.1 from
    member_upper_tree_index hr hn j]

end WaveTurbulence.VineAlign

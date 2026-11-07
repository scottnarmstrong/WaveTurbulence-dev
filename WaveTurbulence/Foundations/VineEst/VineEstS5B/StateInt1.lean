/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Exc
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp16Main

/-! # V5 Step 4d-B: the S-side of the states of `Zp(A)` in the chart of `A` (part 1: split data)

`SplitAt.slow`: the upper block of a split at `p*` has lower joint `b = (placement p*).lower` and kept slot `(placement p*).keep`.
`stw_true`: the upper blocks of `A` and of the output of a TRUE operation at `p*` form an `STw`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

theorem excluded_eq_keep' {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {a' z : GBranch G.tree}
    (ha : a' = P.lower) (hB : G.molecule.IsBlock T a' z) (R : CLRegionData G T a' z) : R.excluded = P.keep := by
  subst ha
  exact excluded_eq_keep P hB R

theorem SplitAt.slow {S : Garden w} {F : CoreFamily S ι} (sp : SplitAt S F pstar J) :
    SLow (F.placement pstar) sp.RS := by
  have hbk : sp.sb.b = (F.placement pstar).lower := sp.joint.trans sp.bk
  have hex : sp.RT.excluded = sp.RS.kept :=
    split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  exact ⟨sp.sb.block, hbk, hex.symm.trans (excluded_eq_keep' _ hbk sp.hT sp.RT)⟩

theorem stw_true (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) :
    STw (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS := by
  have h1 := SplitAt.slow sp
  have h2 := SplitAt.slow (SplitAt.nextA A sp pstar true)
  refine ⟨h1.block, h1.lower, h1.keep, ?_⟩
  refine h2.keep.trans ?_
  exact A.family.nextPlacement_keep pstar pstar

end WaveTurbulence.VineEstS5B

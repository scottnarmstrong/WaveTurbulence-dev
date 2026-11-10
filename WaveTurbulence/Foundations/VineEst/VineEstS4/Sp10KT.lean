/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp9Fib

/-! # The common factor of the lower kernels (V5 Step 4b, step 4, WP-A / WP-C)

`twAt A G pstar`: the operation at `pstar` that gives `G` twisted the skeleton (the sign at the lower joint of `pstar` differs from
the one of `A`).  `kTor`: the lower kernel of `y` with the first two boundary momenta exchanged iff `twAt`.
`kT_rel`: for `x` in the fibre of `G` and `x = (operation at pstar)(y)`, `kT x = kTor G y` (TARGET: "the roles of
`k_{u_2^p}` and `k_{u_23^p}` are switched again").
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- The operation at `pstar` that produced `G` twisted the skeleton. -/
@[expose] def twAt (A G : FamilyReconstruction w ι) (pstar : ι) : Prop := (sigStar G pstar).1 ≠ (sigStar A pstar).1

open Classical in
/-- The lower kernel of `y`, with the first two boundary momenta exchanged iff `G` is a twist at `pstar`. -/
@[expose] noncomputable def kTor (κ : KPar d) (A G : FamilyReconstruction w ι) (pstar : ι) (y : ST w ι pstar J) :
    ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  if twAt A G pstar then kT κ y.1 y.2 t F' E else kT κ y.1 y.2 t E F'

theorem not_twAt_of_eq {A G : FamilyReconstruction w ι} (h : sigStar G pstar = sigStar A pstar) : ¬ twAt A G pstar :=
  fun hh => hh (congrArg Prod.fst h)

section Rel
variable (κ : KPar d) {A : FamilyReconstruction w ι} {sp0 : SplitAt A.skeleton A.family pstar J}

end Rel

end WaveTurbulence.VineEstS4

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.NestGeom

/-! # The bundle of the S-side as an abstract S-integrand (V5 Step 4d part C, WP-I)

`bundleKernel`: the chart-of-`A` integrand of `bundleInt` without its lower factor, as a function of the decoration and the clock;
`psiSB`: its signed sum over `Zp(A)` (TARGET (replaceterm1)).  `sum_stInt_eq`: `∑_G stInt G = psiSB * K̃(σ_b, E, F_r)`, the
S-integrand `ΨS` of the merge `lkRaw_split_fubini`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The integrand of the chart of `A` without the lower factor, as a function of the decoration and the clock. -/
noncomputable def bundleKernel (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (x : GNode A.skeleton.tree → (Fin d → ℤ))
    (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.sb.U sp.sb.a sp.sb.b
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u *
    rowVal ν rq rt (u sp.sb.b)
      (if tw then u (qrOf (A.family.placement pstar)) else u (qbOf (A.family.placement pstar)))
      (if tw then u (qbOf (A.family.placement pstar)) else u (qrOf (A.family.placement pstar)))
      (if tw then κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode)
        else κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode))
      (if tw then κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)
        else κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))

theorem bundleInt_eq_kernel (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (Ψ : ℝ → Mom d → Mom d → ℂ) (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ)
    (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    bundleInt κ A sp Ψ tw ν rq rt x σ =
      bundleKernel κ A sp tw ν rq rt x.1 (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
        Ψ (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b)
          (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).lower.toNode))
          (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).retained.toNode)) := by
  unfold bundleInt bundleKernel
  ring

open Classical in
/-- The bundle of the S-side: the sum over `Zp(A)` of the signed exceptional integrands (TARGET (replaceterm1)). -/
noncomputable def psiSB (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  ∑ G ∈ zpFinset p kind pstar J A sp0 hA, epsOf A pstar G.1 *
    bundleKernel κ A sp0 (decide (twAt A G.1 pstar)) (nuOf G.1 pstar) (rowQ κ G.1 pstar) (rowT κ G.1 pstar) x u

end WaveTurbulence.VineEstS5C

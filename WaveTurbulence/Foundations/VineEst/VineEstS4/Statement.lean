/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.VineEst.VineEstS3.StepMono
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedCont
public import WaveTurbulence.Foundations.VineEst.VineEstS3.PointwiseDecay
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafTrace
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafWire
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClause

/-! # TARGET Proposition `vineest` (L1730-L1752), the full statement with the LF-twist sum (V5 Step 4a)

`VineEstFull P` is `Step3Statement P` with the single-garden kernel `K̃^U_{(G)}` replaced by
`K̃^U = e^{-πiδL^{2γ}t_{u1}Γ} Σ_{G'} K^U_{(G')}` (vineest1), the sum over the gardens `G'` of the twist class (LF twists
of `G` at the chain `U`, `allCoreOutputs` of the core family of its pieces).  The premise `CoreVinesNoTwist` of Step 3
is removed (it is the case in which the class is a singleton, `BaseCase`).

The summand of a garden is the kernel of one representative state reached by a batch (`ClassSection`).  The statement
holds for every choice of representatives, so no independence of the representative is assumed; the sections exist
(`exists_classSection`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree
open scoped ENNReal

/-- (vineest1): `e^{-πiδL^{2γ}t_{u1}Γ} Σ_{G'} K^U_{(G')}`, the sum over the representatives `Z` of the twist class. -/
@[expose] noncomputable def twistedRecentered {w d : ℕ} {ι : Type*} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) *
    Complex.I) *
    ∑ x ∈ Z, twistedLocalKernel x.1 x.2 L γ δ F base tUpper tPositive tNegative e f g h

end WaveTurbulence.VineEstS4

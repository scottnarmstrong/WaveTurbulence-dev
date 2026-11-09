/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyIndex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowUnionEquiv
public import Mathlib.Logic.Equiv.Prod
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChart
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyIndex
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChart` (sha256 799cc46b0e3ffa36…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The actual triangular full-chain M9 chart -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Decode the bottom vine first, then use its literal anchor bond as the
prefix chart's lower momentum. All gluing and inverse maps are proved source
flow equivalences, so no garden parametrization premise is introduced. -/
noncomputable def chainFlowChartΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] (g r : E) :
    FlowFiber G.molecule U a b E r ≃ (chainInputIndexΓ hM9 B → E) := by
  induction B generalizing g with
  | single hV R => exact (chosenVineChartΓ hM9 hV).chart g r
  | @append S T a b c n RP B hT hi hU R ih =>
    let C := chosenVineChartΓ hM9 hT
    let anchor := B.terminalAnchor hT hi hU R
    let split := flowUnionEquiv (E := E) (r := r) (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU
    let prefixEquiv := Equiv.prodCongrRight (fun kT : FlowFiber G.molecule T b c E r => ih (kT.1 anchor))
    exact (split.trans (Equiv.prodComm _ _)).trans
      (prefixEquiv.trans ((Equiv.prodCongr (C.chart g r) (Equiv.refl _)).trans
        (Equiv.sumArrowEquivProdArrow _ _ E).symm))

end WaveTurbulence.GammaLow.Famb.VineEstS2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceStates` (sha256 a3454f9e3ed06d5b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Actual ingredient regions, restricted currents and inherited anchors -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

noncomputable def assemblyRegionAtΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) : ∀ i : Fin n,
      CLRegionData G (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper (assemblyPieceAtΓ B i).lower := by
  induction B with
  | single hV R => exact fun _ => R
  | append B hT hi hU R ih => exact Fin.cases (B.terminalRegion hT hi hU R) ih

noncomputable def assemblyFlowAtΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) : ∀ i : Fin n,
      FlowFiber G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper (assemblyPieceAtΓ B i).lower E r := by
  induction B with
  | single hV R => exact fun _ => k
  | append B hT hi hU R ih =>
    exact Fin.cases (restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k)
      (ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k))

noncomputable def assemblyAnchorAtΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (g : E) : Fin n → E := by
  induction B generalizing g with
  | single hV R => exact fun _ => g
  | append B hT hi hU R ih =>
    let kT := restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k
    exact Fin.cases g (ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k)
      (kT.1 (B.terminalAnchor hT hi hU R)))

end WaveTurbulence.GammaLow.Famb.VineEstS2

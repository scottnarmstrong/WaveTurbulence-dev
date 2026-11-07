/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations

/-! # Actual ingredient regions, restricted currents and inherited anchors -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

noncomputable def assemblyRegionAt
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : ∀ i : Fin n,
      CLRegionData G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower := by
  induction B with
  | single hV R => exact fun _ => R
  | append B hT hi hU R ih => exact Fin.cases (B.terminalRegion hT hi hU R) ih

noncomputable def assemblyFlowAt
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) : ∀ i : Fin n,
      FlowFiber G.molecule (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower E r := by
  induction B with
  | single hV R => exact fun _ => k
  | append B hT hi hU R ih =>
    exact Fin.cases (restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k)
      (ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k))

noncomputable def assemblyAnchorAt
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (g : E) : Fin n → E := by
  induction B generalizing g with
  | single hV R => exact fun _ => g
  | append B hT hi hU R ih =>
    let kT := restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k
    exact Fin.cases g (ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k)
      (kT.1 (B.terminalAnchor hT hi hU R)))

end WaveTurbulence.VineEstS2

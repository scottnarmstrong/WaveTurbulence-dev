/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChart
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChart
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations` (sha256 5f0f3e6264f975fa…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Literal inverse gluing equations of the recursive source chart -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}
variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
variable {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssemblyΓ γF G RP n)
variable (hT : FinalCount.Src.IsSomeVine γF G.molecule T b c) (hi : S ∩ T = {b})
variable (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)
variable (hM9 : NormalChartSupply γF) {E : Type} [AddCommGroup E] (g r : E)

/-- Inverse decoding first reconstructs the terminal bond labels, then
uses their literal anchor value for the prefix, and finally glues them. -/
theorem chainFlowChart_symm_appendΓ
    (x : chainInputIndexΓ hM9 (.append B hT hi hU R) → E) :
    (chainFlowChartΓ hM9 (.append B hT hi hU R) g r).symm x =
      let kT := ((chosenVineChartΓ hM9 hT).chart g r).symm (fun j => x (.inl j))
      let kS := (chainFlowChartΓ hM9 B (kT.1 (B.terminalAnchor hT hi hU R)) r).symm (fun j => x (.inr j))
      glueFlowFiber (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU kS kT := by
  rfl

theorem chainFlowChart_append_inlΓ (k : FlowFiber G.molecule (S ∪ T) a c E r)
    (j : Fin (chosenVineChartΓ hM9 hT).indexing.shape.n) :
    chainFlowChartΓ hM9 (.append B hT hi hU R) g r k (.inl j) =
      (chosenVineChartΓ hM9 hT).chart g r
        (restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k) j := rfl

theorem chainFlowChart_append_inrΓ (k : FlowFiber G.molecule (S ∪ T) a c E r)
    (j : chainInputIndexΓ hM9 B) :
    chainFlowChartΓ hM9 (.append B hT hi hU R) g r k (.inr j) =
      chainFlowChartΓ hM9 B
        ((restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k).1
          (B.terminalAnchor hT hi hU R)) r
        (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k) j := rfl

end WaveTurbulence.GammaLow.Famb.VineEstS2

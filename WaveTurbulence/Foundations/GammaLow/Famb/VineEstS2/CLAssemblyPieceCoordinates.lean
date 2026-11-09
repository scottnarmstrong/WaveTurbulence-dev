/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyInputEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyInputEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceStates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceCoordinates` (sha256 10236c290d88018c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Ingredient charts use the literal block slices of the full-chain input -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- The current and anchor inherited at every source ingredient reproduce
exactly its own coordinates, in the original bottom-to-top family order. -/
theorem assembly_piece_coordinateΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (g : E) :
    ∀ (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n),
      (assemblyChartAtΓ hM9 B i).chart (assemblyAnchorAtΓ B k g i) r (assemblyFlowAtΓ B k i) j =
        chainFlowChartΓ hM9 B g r k ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩) := by
  induction B generalizing g with
  | single hV R =>
    intro i j
    rw [assemblyInputEquiv_single_symmΓ]
    rfl
  | append B hT hi hU R ih =>
    intro i
    refine Fin.cases ?_ (fun i => ?_) i <;> intro j
    · exact (chainFlowChart_append_inlΓ B hT hi hU R hM9 g r k j).symm
    · exact (ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k)
        ((restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k).1 (B.terminalAnchor hT hi hU R)) i j).trans
        (chainFlowChart_append_inrΓ B hT hi hU R hM9 g r k ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩)).symm

/-- The inverse fiber of each ingredient is its checked M9 chart at the
corresponding slice of the actual full-chain input. -/
theorem assembly_piece_flow_eq_chart_symmΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (g : E) (i : Fin n) :
    assemblyFlowAtΓ B k i =
      ((assemblyChartAtΓ hM9 B i).chart (assemblyAnchorAtΓ B k g i) r).symm
        (fun j => chainFlowChartΓ hM9 B g r k ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩)) := by
  apply ((assemblyChartAtΓ hM9 B i).chart (assemblyAnchorAtΓ B k g i) r).injective
  rw [Equiv.apply_symm_apply]
  funext j
  exact assembly_piece_coordinateΓ hM9 B k g i j

end WaveTurbulence.GammaLow.Famb.VineEstS2

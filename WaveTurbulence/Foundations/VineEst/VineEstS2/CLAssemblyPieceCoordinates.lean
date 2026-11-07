/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyInputEquations

/-! # Ingredient charts use the literal block slices of the full-chain input -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- The current and anchor inherited at every source ingredient reproduce
exactly its own coordinates, in the original bottom-to-top family order. -/
theorem assembly_piece_coordinate (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (g : E) :
    ∀ (i : Fin n) (j : Fin (assemblyChartAt hM9 B i).indexing.shape.n),
      (assemblyChartAt hM9 B i).chart (assemblyAnchorAt B k g i) r (assemblyFlowAt B k i) j =
        chainFlowChart hM9 B g r k ((assemblyInputEquiv hM9 B).symm ⟨i,j⟩) := by
  induction B generalizing g with
  | single hV R =>
    intro i j
    rw [assemblyInputEquiv_single_symm]
    rfl
  | append B hT hi hU R ih =>
    intro i
    refine Fin.cases ?_ (fun i => ?_) i <;> intro j
    · exact (chainFlowChart_append_inl B hT hi hU R hM9 g r k j).symm
    · exact (ih (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k)
        ((restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k).1 (B.terminalAnchor hT hi hU R)) i j).trans
        (chainFlowChart_append_inr B hT hi hU R hM9 g r k ((assemblyInputEquiv hM9 B).symm ⟨i,j⟩)).symm

/-- The inverse fiber of each ingredient is its checked M9 chart at the
corresponding slice of the actual full-chain input. -/
theorem assembly_piece_flow_eq_chart_symm (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) {E : Type} [AddCommGroup E] {r : E}
    (k : FlowFiber G.molecule U a b E r) (g : E) (i : Fin n) :
    assemblyFlowAt B k i =
      ((assemblyChartAt hM9 B i).chart (assemblyAnchorAt B k g i) r).symm
        (fun j => chainFlowChart hM9 B g r k ((assemblyInputEquiv hM9 B).symm ⟨i,j⟩)) := by
  apply ((assemblyChartAt hM9 B i).chart (assemblyAnchorAt B k g i) r).injective
  rw [Equiv.apply_symm_apply]
  funext j
  exact assembly_piece_coordinate hM9 B k g i j

end WaveTurbulence.VineEstS2

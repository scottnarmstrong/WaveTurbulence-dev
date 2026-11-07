/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChart

/-! # Literal inverse gluing equations of the recursive source chart -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}
variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
variable {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssembly G RP n)
variable {X : VineType} (hT : G.molecule.IsVine X T b c) (hi : S ∩ T = {b})
variable (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)
variable (hM9 : VINEPARAM) {E : Type} [AddCommGroup E] (g r : E)

/-- Inverse decoding first reconstructs the terminal bond labels, then
uses their literal anchor value for the prefix, and finally glues them. -/
theorem chainFlowChart_symm_append
    (x : chainInputIndex hM9 (.append B hT hi hU R) → E) :
    (chainFlowChart hM9 (.append B hT hi hU R) g r).symm x =
      let kT := ((chosenVineChart hM9 X hT).chart g r).symm (fun j => x (.inl j))
      let kS := (chainFlowChart hM9 B (kT.1 (B.terminalAnchor hT hi hU R)) r).symm (fun j => x (.inr j))
      glueFlowFiber (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU kS kT := by
  rfl

theorem chainFlowChart_append_inl (k : FlowFiber G.molecule (S ∪ T) a c E r)
    (j : Fin (chosenVineChart hM9 X hT).indexing.shape.n) :
    chainFlowChart hM9 (.append B hT hi hU R) g r k (.inl j) =
      (chosenVineChart hM9 X hT).chart g r
        (restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k) j := rfl

theorem chainFlowChart_append_inr (k : FlowFiber G.molecule (S ∪ T) a c E r)
    (j : chainInputIndex hM9 B) :
    chainFlowChart hM9 (.append B hT hi hU R) g r k (.inr j) =
      chainFlowChart hM9 B
        ((restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k).1
          (B.terminalAnchor hT hi hU R)) r
        (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU k) j := rfl

end WaveTurbulence.VineEstS2

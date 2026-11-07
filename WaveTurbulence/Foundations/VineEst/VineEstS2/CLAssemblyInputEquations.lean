/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces

/-! # Literal block index equations for the source-chain coordinate change -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

 theorem assemblyInputEquiv_single_symm (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {X : VineType}
    (hV : G.molecule.IsVine X U a b) (R : CLRegionData G U a b) (i : Fin 1)
    (j : Fin (assemblyChartAt hM9 (.single hV R) i).indexing.shape.n) :
    (assemblyInputEquiv hM9 (.single hV R)).symm ⟨i,j⟩ = j := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
variable {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssembly G RP n)
variable {X : VineType} (hT : G.molecule.IsVine X T b c) (hi : S ∩ T = {b})
variable (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)

theorem assemblyInputEquiv_append_zero_symm (hM9 : VINEPARAM)
    (j : Fin (assemblyChartAt hM9 (.append B hT hi hU R) 0).indexing.shape.n) :
    (assemblyInputEquiv hM9 (.append B hT hi hU R)).symm ⟨0,j⟩ = .inl j := rfl

theorem assemblyInputEquiv_append_succ_symm (hM9 : VINEPARAM) (i : Fin n)
    (j : Fin (assemblyChartAt hM9 B i).indexing.shape.n) :
    (assemblyInputEquiv hM9 (.append B hT hi hU R)).symm ⟨i.succ,j⟩ =
      .inr ((assemblyInputEquiv hM9 B).symm ⟨i,j⟩) := rfl

end WaveTurbulence.VineEstS2

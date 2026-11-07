/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintRows

/-! # The matrix rows are the literal original source lattice labels -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem clChain_pair_matrix_value {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM) (hG : G.IsPlain)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShape hM9 B).VIdx) :
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    assemblyPairValue hM9 B hG (clExtendIndices R κ.1) v =
      β 2 + (∑ j, assemblyPairMatrix hM9 B hG v j • x j) +
        chainDecodeGap hM9 B (clOrderedPairBond B.isBlock R hG (assemblyPairOrder hG B hM9) ((assemblyRowEquiv hM9 B).symm v)) • (β 2-β 3) := by
  let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
  have hv := clOrderedPairBond_value B.isBlock R hG (assemblyPairOrder hG B hM9) ((assemblyRowEquiv hM9 B).symm v)
    (clExtendIndices R κ.1) κ.2.2.1
  have hd := clChainCoordinateEquiv_bond hL B base β hβ hM9 x
    (clOrderedPairBond B.isBlock R hG (assemblyPairOrder hG B hM9) ((assemblyRowEquiv hM9 B).symm v))
  change _ = assemblyPairValue hM9 B hG (clExtendIndices R κ.1) v at hv
  calc
    _ = _ := hv.symm
    _ = _ := hd
    _ = _ := by
      congr 2
      simpa only [assemblyPairMatrix,Equiv.symm_apply_apply] using
        (assemblyVectorEquiv hM9 B).sum_comp (fun j => assemblyPairMatrix hM9 B hG v j • x j)

theorem clChain_branch_matrix_value {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShape hM9 B).VIdx) :
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    assemblyBranchValue hM9 B (clExtendIndices R κ.1) v =
      β 2 + (∑ j, assemblyBranchMatrix hM9 B v j • x j) +
        chainDecodeGap hM9 B (clOrderedBranchBond B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v)) • (β 2-β 3) := by
  let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
  have hv := clOrderedBranchBond_value B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v)
    (clExtendIndices R κ.1) κ.2.2.1
  have hd := clChainCoordinateEquiv_bond hL B base β hβ hM9 x
    (clOrderedBranchBond B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v))
  change _ = assemblyBranchValue hM9 B (clExtendIndices R κ.1) v at hv
  calc
    _ = _ := hv.symm
    _ = _ := hd
    _ = _ := by
      congr 2
      simpa only [assemblyBranchMatrix,Equiv.symm_apply_apply] using
        (assemblyVectorEquiv hM9 B).sum_comp (fun j => assemblyBranchMatrix hM9 B v j • x j)

end WaveTurbulence.VineEstS2

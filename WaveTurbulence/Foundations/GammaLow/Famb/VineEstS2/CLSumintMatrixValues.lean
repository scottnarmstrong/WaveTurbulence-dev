/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintRows
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrixValues` (sha256 415b1ff6acdd0a89…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The matrix rows are the literal original source lattice labels -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem clChain_pair_matrix_valueΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF) (hG : G.IsPlain)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    assemblyPairValueΓ hM9 B hG (clExtendIndices R κ.1) v =
      β 2 + (∑ j, assemblyPairMatrixΓ hM9 B hG v j • x j) +
        chainDecodeGapΓ hM9 B (clOrderedPairBond B.isBlock R hG (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v)) • (β 2-β 3) := by
  let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
  have hv := clOrderedPairBond_value B.isBlock R hG (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v)
    (clExtendIndices R κ.1) κ.2.2.1
  have hd := clChainCoordinateEquiv_bondΓ hL B base β hβ hM9 x
    (clOrderedPairBond B.isBlock R hG (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v))
  change _ = assemblyPairValueΓ hM9 B hG (clExtendIndices R κ.1) v at hv
  calc
    _ = _ := hv.symm
    _ = _ := hd
    _ = _ := by
      congr 2
      simpa only [assemblyPairMatrixΓ,Equiv.symm_apply_apply] using
        (assemblyVectorEquivΓ hM9 B).sum_comp (fun j => assemblyPairMatrixΓ hM9 B hG v j • x j)

theorem clChain_branch_matrix_valueΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1) v =
      β 2 + (∑ j, assemblyBranchMatrixΓ hM9 B v j • x j) +
        chainDecodeGapΓ hM9 B (clOrderedBranchBond B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v)) • (β 2-β 3) := by
  let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
  have hv := clOrderedBranchBond_value B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v)
    (clExtendIndices R κ.1) κ.2.2.1
  have hd := clChainCoordinateEquiv_bondΓ hL B base β hβ hM9 x
    (clOrderedBranchBond B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v))
  change _ = assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1) v at hv
  calc
    _ = _ := hv.symm
    _ = _ := hd
    _ = _ := by
      congr 2
      simpa only [assemblyBranchMatrixΓ,Equiv.symm_apply_apply] using
        (assemblyVectorEquivΓ hM9 B).sum_comp (fun j => assemblyBranchMatrixΓ hM9 B v j • x j)

end WaveTurbulence.GammaLow.Famb.VineEstS2

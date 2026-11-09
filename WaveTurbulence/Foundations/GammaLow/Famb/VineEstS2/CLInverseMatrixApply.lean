/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixData
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixApply
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixData
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrixValues
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixApply` (sha256 fb7438bb03427e1e…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The unit inverse rows invert the actual source pair decoder -/

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

/-- The matrix identity is tested on all genuine local decorations at zero
boundary values, rather than inferred from a count of variables. -/
theorem assemblyInversePairMatrix_applyΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    x v = ∑ p, assemblyInversePairMatrixΓ hM9 B hG v p • (∑ j, assemblyPairMatrixΓ hM9 B hG p j • x j) := by
  have hβ : ((G.sign a.toNode : ℤ) • ((0 : Fin 4 → (Fin d → ℤ)) 0-0)) = 0-0 := by simp
  let κ := (clChainCoordinateEquivΓ (L := 1) one_ne_zero B (0 : Mom d) 0 hβ hM9).symm x
  let e := (assemblyPairOrderΓ hG B hM9).trans (assemblyRowEquivΓ hM9 B)
  have hp (p : ↥(clRegionalPairs hG U)) : clOriginValue B.isBlock R hG (clExtendIndices R κ.1) (.inl p) =
      ∑ j, assemblyPairMatrixΓ hM9 B hG (e p) j • x j := by
    have he := clChain_pair_matrix_valueΓ (L := 1) one_ne_zero B (0 : Mom d) 0 hβ hM9 hG x (e p)
    simpa only [e,Equiv.trans_apply,assemblyPairValueΓ,clOrderedPairValue,Equiv.symm_apply_apply,
      Pi.zero_apply,sub_self,smul_zero,add_zero,zero_add] using he
  have hbound (c : Fin 4) : clOriginValue B.isBlock R hG (clExtendIndices R κ.1) (.inr c) = 0 :=
    latticePoint_injective_of_ne_zero one_ne_zero (add_left_cancel (κ.2.2.2 c))
  have hi := chainInverseCoeff_identityΓ hM9 B hG ((assemblyVectorEquivΓ hM9 B).symm v)
    (L := 1) one_ne_zero (0 : Mom d) 0 hβ x
  change x (assemblyVectorEquivΓ hM9 B ((assemblyVectorEquivΓ hM9 B).symm v)) =
    ∑ o, chainInverseCoeffΓ hM9 B hG ((assemblyVectorEquivΓ hM9 B).symm v) o •
      clOriginValue B.isBlock R hG (clExtendIndices R κ.1) o at hi
  rw [Fintype.sum_sum_type] at hi
  simp only [hp,hbound,smul_zero,Finset.sum_const_zero,add_zero,Equiv.apply_symm_apply] at hi
  calc
    _ = _ := hi
    _ = _ := by
      have he := e.sum_comp (fun p => assemblyInversePairMatrixΓ hM9 B hG v p •
        (∑ j, assemblyPairMatrixΓ hM9 B hG p j • x j))
      simpa only [assemblyInversePairMatrixΓ,e,Equiv.trans_apply,Equiv.symm_apply_apply] using he

end WaveTurbulence.GammaLow.Famb.VineEstS2

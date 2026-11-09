/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceTags
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAffineBoundaryRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceAffineRows` (sha256 da16033412e360d6…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Affine forms of the actual pair, branch and lower-boundary tags -/

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

noncomputable def sourceRowTΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    CLSourceOrigin R → (assemblyShapeΓ hM9 B).VIdx → ℤ
  | .inl p => assemblyPairMatrixΓ hM9 B hG (assemblyRowEquivΓ hM9 B p)
  | .inr (.inl v) => assemblyBranchMatrixΓ hM9 B (assemblyRowEquivΓ hM9 B v)
  | .inr (.inr _) => 0

noncomputable def sourceRowHΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    CLSourceOrigin R → Fin 4 → ℤ
  | .inl p => assemblyPairBoundaryRowΓ hM9 B hG (assemblyRowEquivΓ hM9 B p)
  | .inr (.inl v) => assemblyBranchBoundaryRowΓ hM9 B (assemblyRowEquivΓ hM9 B v)
  | .inr (.inr c) => Pi.single c 1

theorem sourceRowH_chartTag_upper_zeroΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (o : CLChartSourceTag R) : sourceRowHΓ hM9 B hG (chartSourceTag R o) 0 = 0 := by
  cases o with
  | inl o =>
    cases o with
    | inl p => exact assemblyPairBoundaryRow_zeroΓ hM9 B hG _
    | inr v => exact assemblyBranchBoundaryRow_zeroΓ hM9 B _
  | inr j =>
    by_cases hj : j = 0 <;> simp [sourceRowHΓ,chartSourceTag,hj,Pi.single_apply]

theorem chartSource_origin_affineΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF) (hG : G.IsPlain)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (o : CLChartSourceTag R) :
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    clSourceOriginValue B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) (clExtendIndices R κ.1) (chartSourceTag R o) =
      (∑ j, sourceRowTΓ hM9 B hG (chartSourceTag R o) j • x j) +
        ∑ c, sourceRowHΓ hM9 B hG (chartSourceTag R o) c • β c := by
  cases o with
  | inl o =>
    cases o with
    | inl p =>
      simpa only [sourceRowTΓ,sourceRowHΓ,chartSourceTag,interiorSourceTag,clSourceOriginValue,
        assemblyPairValueΓ,Equiv.symm_apply_apply] using
        clChain_pair_affine_valueΓ hL B base β hβ hM9 hG x (assemblyRowEquivΓ hM9 B p)
    | inr v =>
      simpa only [sourceRowTΓ,sourceRowHΓ,chartSourceTag,interiorSourceTag,clSourceOriginValue,
        assemblyBranchValueΓ,Equiv.symm_apply_apply] using
        clChain_branch_affine_valueΓ hL B base β hβ hM9 x (assemblyRowEquivΓ hM9 B v)
  | inr j =>
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    have hb : clExtendIndices R κ.1 (clBoundaryNodes R (if j = 0 then 2 else 3)) = β (if j = 0 then 2 else 3) :=
      latticePoint_injective_of_ne_zero hL (add_left_cancel (κ.2.2.2 _))
    simpa [sourceRowTΓ,sourceRowHΓ,chartSourceTag,clSourceOriginValue,Pi.single_apply] using hb

end WaveTurbulence.GammaLow.Famb.VineEstS2

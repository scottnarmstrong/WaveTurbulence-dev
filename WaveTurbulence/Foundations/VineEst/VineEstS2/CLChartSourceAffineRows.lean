/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceTags
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows

/-! # Affine forms of the actual pair, branch and lower-boundary tags -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def sourceRowT (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    CLSourceOrigin R → (assemblyShape hM9 B).VIdx → ℤ
  | .inl p => assemblyPairMatrix hM9 B hG (assemblyRowEquiv hM9 B p)
  | .inr (.inl v) => assemblyBranchMatrix hM9 B (assemblyRowEquiv hM9 B v)
  | .inr (.inr _) => 0

noncomputable def sourceRowH (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    CLSourceOrigin R → Fin 4 → ℤ
  | .inl p => assemblyPairBoundaryRow hM9 B hG (assemblyRowEquiv hM9 B p)
  | .inr (.inl v) => assemblyBranchBoundaryRow hM9 B (assemblyRowEquiv hM9 B v)
  | .inr (.inr c) => Pi.single c 1

theorem sourceRowH_chartTag_upper_zero (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (o : CLChartSourceTag R) : sourceRowH hM9 B hG (chartSourceTag R o) 0 = 0 := by
  cases o with
  | inl o =>
    cases o with
    | inl p => exact assemblyPairBoundaryRow_zero hM9 B hG _
    | inr v => exact assemblyBranchBoundaryRow_zero hM9 B _
  | inr j =>
    by_cases hj : j = 0 <;> simp [sourceRowH,chartSourceTag,hj,Pi.single_apply]

theorem chartSource_origin_affine {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM) (hG : G.IsPlain)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (o : CLChartSourceTag R) :
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    clSourceOriginValue B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (clExtendIndices R κ.1) (chartSourceTag R o) =
      (∑ j, sourceRowT hM9 B hG (chartSourceTag R o) j • x j) +
        ∑ c, sourceRowH hM9 B hG (chartSourceTag R o) c • β c := by
  cases o with
  | inl o =>
    cases o with
    | inl p =>
      simpa only [sourceRowT,sourceRowH,chartSourceTag,interiorSourceTag,clSourceOriginValue,
        assemblyPairValue,Equiv.symm_apply_apply] using
        clChain_pair_affine_value hL B base β hβ hM9 hG x (assemblyRowEquiv hM9 B p)
    | inr v =>
      simpa only [sourceRowT,sourceRowH,chartSourceTag,interiorSourceTag,clSourceOriginValue,
        assemblyBranchValue,Equiv.symm_apply_apply] using
        clChain_branch_affine_value hL B base β hβ hM9 x (assemblyRowEquiv hM9 B v)
  | inr j =>
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    have hb : clExtendIndices R κ.1 (clBoundaryNodes R (if j = 0 then 2 else 3)) = β (if j = 0 then 2 else 3) :=
      latticePoint_injective_of_ne_zero hL (add_left_cancel (κ.2.2.2 _))
    simpa [sourceRowT,sourceRowH,chartSourceTag,clSourceOriginValue,Pi.single_apply] using hb

end WaveTurbulence.VineEstS2

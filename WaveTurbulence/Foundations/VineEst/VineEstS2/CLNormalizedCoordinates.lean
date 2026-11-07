/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLCoordinateSourceDifferences
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintJointFlip
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices

/-! # Regional lattice coordinates with the frozen sumint gap convention -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def clNormalizedChainEquiv {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM) :
    CLLocalDecoration R L base (fun j => base+latticePoint L (β j)) ≃
      ((assemblyShape hM9 B).VIdx → (Fin d → ℤ)) :=
  (clChainCoordinateEquiv hL B base β hβ hM9).trans (jointFlip _)

noncomputable def normalizedPairMatrix (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    Matrix (assemblyShape hM9 B).VIdx (assemblyShape hM9 B).VIdx ℤ :=
  fun v j => assemblyPairMatrix hM9 B hG v j * jointFlipSign _ j

noncomputable def normalizedBranchMatrix (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    Matrix (assemblyShape hM9 B).VIdx (assemblyShape hM9 B).VIdx ℤ :=
  fun v j => assemblyBranchMatrix hM9 B v j * jointFlipSign _ j

theorem normalizedPairMatrix_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v j : (assemblyShape hM9 B).VIdx) : IsUnitCoeff (normalizedPairMatrix hM9 B hG v j) :=
  jointFlip_unit _ _ _ (assemblyPairMatrix_unit hM9 B hG v j)

theorem normalizedBranchMatrix_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v j : (assemblyShape hM9 B).VIdx) : IsUnitCoeff (normalizedBranchMatrix hM9 B v j) :=
  jointFlip_unit _ _ _ (assemblyBranchMatrix_unit hM9 B v j)

/-- Negating a joint coordinate merely swaps its two actual source
origins; every rung and core coordinate retains its original difference. -/
theorem clNormalizedChain_source_difference (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (i : (assemblyShape hM9 B).VIdx) :
    ∃ p q : CLSourceOrigin R,
      ∀ {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
        (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
        (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)),
        let κ := (clNormalizedChainEquiv hL B base β hβ hM9).symm x
        x i = clSourceOriginValue B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (clExtendIndices R κ.1) p -
          clSourceOriginValue B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (clExtendIndices R κ.1) q := by
  obtain ⟨p,q,hpq⟩ := clChainCoordinate_source_difference hM9 B hG i
  by_cases hi : i.2.val = 0
  · refine ⟨q,p,?_⟩
    intro d L hL base β hβ x
    have he := hpq hL base β hβ (jointFlip _ x)
    have hh := congrArg (fun y : Fin d → ℤ => -y) he
    simpa only [clNormalizedChainEquiv,Equiv.symm_trans_apply,jointFlip,jointFlipSign,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,hi,ite_true,neg_one_zsmul,neg_neg,neg_sub]
      using hh
  · refine ⟨p,q,?_⟩
    intro d L hL base β hβ x
    have he := hpq hL base β hβ (jointFlip _ x)
    simpa only [clNormalizedChainEquiv,Equiv.symm_trans_apply,jointFlip,jointFlipSign,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,hi,ite_false,one_smul] using he

end WaveTurbulence.VineEstS2

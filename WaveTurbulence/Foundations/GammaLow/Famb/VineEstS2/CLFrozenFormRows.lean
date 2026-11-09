/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenFormRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenFormRows` (sha256 7b48a401c67d7db8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact row expressions appearing in frozen sumint hypothesis (iii) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def chartSourceFrozenTagΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    CLChartSourceTag R → (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx ⊕ Fin 4
  | .inl (.inl p) => .inl (assemblyRowEquivΓ hM9 B p)
  | .inl (.inr v) => .inr (.inl (assemblyRowEquivΓ hM9 B v))
  | .inr j => .inr (.inr (if j = 0 then 2 else 3))

theorem formRowT_chartSourceTagΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (o : CLChartSourceTag R) :
    sumintFormRowT (assemblyPairMatrixΓ hM9 B hG) (assemblyBranchMatrixΓ hM9 B) (chartSourceFrozenTagΓ hM9 B o) =
      sourceRowTΓ hM9 B hG (chartSourceTag R o) := by
  rcases o with (p | v) | j <;> rfl

theorem formRowH_chartSourceTagΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (o : CLChartSourceTag R) :
    sumintFormRowH (assemblyPairBoundaryRowΓ hM9 B hG) (assemblyBranchBoundaryRowΓ hM9 B) (chartSourceFrozenTagΓ hM9 B o) =
      sourceRowHΓ hM9 B hG (chartSourceTag R o) := by
  rcases o with (p | v) | j <;> rfl

theorem normalized_formRowTΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (o : (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx ⊕ Fin 4)
    (j : (assemblyShapeΓ hM9 B).VIdx) :
    sumintFormRowT (normalizedPairMatrixΓ hM9 B hG) (normalizedBranchMatrixΓ hM9 B) o j =
      sumintFormRowT (assemblyPairMatrixΓ hM9 B hG) (assemblyBranchMatrixΓ hM9 B) o j * jointFlipSign _ j := by
  rcases o with p | v | c
  · rfl
  · rfl
  · exact (zero_mul _).symm

end WaveTurbulence.GammaLow.Famb.VineEstS2

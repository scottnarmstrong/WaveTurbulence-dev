/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainInverseRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixData
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainInverseRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrices
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixData` (sha256 36e346f04c22421e…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Unit integer inverse matrix selected from proved source rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def chainInverseCoeffΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (i : chainInputIndexΓ hM9 B) : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ :=
  Classical.choose (exists_chainInverseRowΓ hM9 B hG i)

theorem chainInverseCoeff_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (i : chainInputIndexΓ hM9 B) (o : ↥(clRegionalPairs hG U) ⊕ Fin 4) : IsUnitCoeff (chainInverseCoeffΓ hM9 B hG i o) :=
  (Classical.choose_spec (exists_chainInverseRowΓ hM9 B hG i)).1 o

theorem chainInverseCoeff_identityΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (i : chainInputIndexΓ hM9 B) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) :
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    x (assemblyVectorEquivΓ hM9 B i) = ∑ o, chainInverseCoeffΓ hM9 B hG i o •
      clOriginValue B.isBlock R hG (clExtendIndices R κ.1) o :=
  (Classical.choose_spec (exists_chainInverseRowΓ hM9 B hG i)).2 hL base β hβ x

noncomputable def assemblyInversePairMatrixΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    Matrix (assemblyShapeΓ hM9 B).VIdx (assemblyShapeΓ hM9 B).VIdx ℤ :=
  fun v p => chainInverseCoeffΓ hM9 B hG ((assemblyVectorEquivΓ hM9 B).symm v)
    (.inl ((assemblyPairOrderΓ hG B hM9).symm ((assemblyRowEquivΓ hM9 B).symm p)))

theorem assemblyInversePairMatrix_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v p : (assemblyShapeΓ hM9 B).VIdx) : IsUnitCoeff (assemblyInversePairMatrixΓ hM9 B hG v p) :=
  chainInverseCoeff_unitΓ hM9 B hG _ _

end WaveTurbulence.GammaLow.Famb.VineEstS2

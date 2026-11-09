/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedPredecessorSystem
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLFrozenAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedPredecessorSystem
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum` (sha256 8c5b4008bb060aa8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The exact frozen sumint datum with proved source linear algebra -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Coefficients after replacing r_source by -r_frozen. Free coefficients
change sign, while the coefficient of r itself is retained. -/
noncomputable def assemblyZetaΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (i : Fin n) (j : Fin ((assemblyChartAtΓ hM9 B i).indexing.shape.m)) (c : Fin 3) : ℤ :=
  if c = 2 then (assemblyChartAtΓ hM9 B i).ζc j c else -(assemblyChartAtΓ hM9 B i).ζc j c

noncomputable def assemblyXiΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (i : Fin n) (c : Fin 4) : ℤ :=
  if c = 3 then (assemblyChartAtΓ hM9 B i).ξc c else -(assemblyChartAtΓ hM9 B i).ξc c

/-- This is the actual frozen carrier and constructor. All matrix proof
fields come from proved regional source identities, not metadata premises. -/
noncomputable def sourceSumintDatumΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) : SumintDatum d where
  S := assemblyShapeΓ hM9 B
  T₁ := normalizedPairMatrixΓ hM9 B hG
  T₁inv := normalizedInversePairMatrixΓ hM9 B hG
  T₂ := normalizedBranchMatrixΓ hM9 B
  T₁_mul := normalizedPairMatrix_mul_inverseΓ hM9 B hG
  T₁inv_mul := normalizedInversePairMatrix_mulΓ hM9 B hG
  T_unit v j := ⟨normalizedPairMatrix_unitΓ hM9 B hG v j,normalizedInversePairMatrix_unitΓ hM9 B hG v j,
    normalizedBranchMatrix_unitΓ hM9 B v j⟩
  H₁ := assemblyPairBoundaryRowΓ hM9 B hG
  H₂ := assemblyBranchBoundaryRowΓ hM9 B
  H_coset := assemblyBoundaryRows_cosetΓ hM9 B hG
  Λ := assemblyBudgetΓ hM9 B
  prev := assemblyPrevΓ hM9 B
  σk v p := assemblyCoeffΓ hM9 B hG v (.inl p)
  σe v c := assemblyCoeffΓ hM9 B hG v (.inr c)
  wK := W.wK
  wL := W.wL
  g := W.g
  g' := W.g'
  ζc := assemblyZetaΓ hM9 B
  Λsel i := (assemblyChartAtΓ hM9 B i).coreLinear
  ξc := assemblyXiΓ hM9 B
  param := W.param
  q := W.q
  constraints := W.constraints
  badKind := W.badKind
  qOut := W.qOut
  centre := W.centre
  wBar := W.wBar

end WaveTurbulence.GammaLow.Famb.VineEstS2

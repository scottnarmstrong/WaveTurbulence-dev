/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedPredecessorSystem
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenAffineDifferences

/-! # The exact frozen sumint datum with proved source linear algebra -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Remaining weight/window data are genuine typing data: no linear or
source reparametrization conclusion is assumed. Their analytic bounds and
bad-case alternatives belong to the later extraction/application step. -/
structure SumintWeightClockData (S : SumintShape) (d : ℕ) where
  wK : S.VIdx → Mom d → ℂ
  wL : S.VIdx → Mom d → ℂ
  g : S.VIdx → ℕ
  g' : S.VIdx → ℕ
  param : S.TVar → ℝ
  q : S.TVar → ℕ
  constraints : Finset (S.TVar × S.TVar)
  badKind : Fin S.I → Fin 4
  qOut : Fin 3 → ℕ
  centre : Fin 4 → Mom d
  wBar : Mom d

/-- Coefficients after replacing r_source by -r_frozen. Free coefficients
change sign, while the coefficient of r itself is retained. -/
noncomputable def assemblyZeta (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (i : Fin n) (j : Fin ((assemblyChartAt hM9 B i).indexing.shape.m)) (c : Fin 3) : ℤ :=
  if c = 2 then (assemblyChartAt hM9 B i).ζc j c else -(assemblyChartAt hM9 B i).ζc j c

noncomputable def assemblyXi (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (i : Fin n) (c : Fin 4) : ℤ :=
  if c = 3 then (assemblyChartAt hM9 B i).ξc c else -(assemblyChartAt hM9 B i).ξc c

/-- This is the actual frozen carrier and constructor. All matrix proof
fields come from proved regional source identities, not metadata premises. -/
noncomputable def sourceSumintDatum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) : SumintDatum d where
  S := assemblyShape hM9 B
  T₁ := normalizedPairMatrix hM9 B hG
  T₁inv := normalizedInversePairMatrix hM9 B hG
  T₂ := normalizedBranchMatrix hM9 B
  T₁_mul := normalizedPairMatrix_mul_inverse hM9 B hG
  T₁inv_mul := normalizedInversePairMatrix_mul hM9 B hG
  T_unit v j := ⟨normalizedPairMatrix_unit hM9 B hG v j,normalizedInversePairMatrix_unit hM9 B hG v j,
    normalizedBranchMatrix_unit hM9 B v j⟩
  H₁ := assemblyPairBoundaryRow hM9 B hG
  H₂ := assemblyBranchBoundaryRow hM9 B
  H_coset := assemblyBoundaryRows_coset hM9 B hG
  Λ := assemblyBudget hM9 B
  prev := assemblyPrev hM9 B
  σk v p := assemblyCoeff hM9 B hG v (.inl p)
  σe v c := assemblyCoeff hM9 B hG v (.inr c)
  wK := W.wK
  wL := W.wL
  g := W.g
  g' := W.g'
  ζc := assemblyZeta hM9 B
  Λsel i := (assemblyChartAt hM9 B i).coreLinear
  ξc := assemblyXi hM9 B
  param := W.param
  q := W.q
  constraints := W.constraints
  badKind := W.badKind
  qOut := W.qOut
  centre := W.centre
  wBar := W.wBar

end WaveTurbulence.VineEstS2

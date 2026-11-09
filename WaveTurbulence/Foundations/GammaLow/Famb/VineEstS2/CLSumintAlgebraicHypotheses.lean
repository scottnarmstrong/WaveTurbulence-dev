/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintAlgebraicHypotheses
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLLinearSumintDatum
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintAlgebraicHypotheses` (sha256 402c59b7f6a44830…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact algebraic hypotheses of the frozen signed sumint consumer -/

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

private theorem coeff_neg {a : ℤ} (h : IsUnitCoeff a) : IsUnitCoeff (-a) := by
  rcases h with h | h | h <;> norm_num [h,IsUnitCoeff]

theorem assemblyZeta_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (i : Fin n) (j : Fin ((assemblyChartAtΓ hM9 B i).indexing.shape.m)) (c : Fin 3) :
    IsUnitCoeff (assemblyZetaΓ hM9 B i j c) := by
  unfold assemblyZetaΓ
  split
  · exact (assemblyChartAtΓ hM9 B i).ζ_unit j c
  · exact coeff_neg ((assemblyChartAtΓ hM9 B i).ζ_unit j c)

theorem assemblyXi_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (i : Fin n) (c : Fin 4) :
    IsUnitCoeff (assemblyXiΓ hM9 B i c) := by
  unfold assemblyXiΓ
  split
  · exact (assemblyChartAtΓ hM9 B i).ξ_unit c
  · exact coeff_neg ((assemblyChartAtΓ hM9 B i).ξ_unit c)

/-- The exact frozen datum satisfies every algebraic clause without any
hypothesis about a proposed reparametrization or a desired conclusion. -/
theorem sourceSumintDatum_algebraic_hypothesesΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) :
    SumintAlgebraicHypotheses (sourceSumintDatumΓ hM9 B hG W) 6561 := by
  have hp := normalized_predecessor_systemΓ hM9 B hG
  exact ⟨hp.1,hp.2.1,hp.2.2,normalized_affine_difference_systemΓ hM9 B hG,
    assemblyZeta_unitΓ hM9 B,assemblyXi_unitΓ hM9 B⟩

noncomputable def assemblyCoreFirstSignΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (i : Fin n) : ℤˣ :=
  (assemblyChartAtΓ hM9 B i).coreFirstSign

noncomputable def assemblyCoreSignΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (i : Fin n) : ℤˣ :=
  (assemblyChartAtΓ hM9 B i).coreSign

end WaveTurbulence.GammaLow.Famb.VineEstS2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At` (sha256 2fc56237b77248cb…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Step 3 at a fixed parameter `P`: the engine bound for the vine-chain kernel with `ε`

`step3D`/`step3Bound` (the datum and engine bound of TARGET vineest Step 3, L1826-L1870, before the constant bookkeeping): at parameters `P` for which the
`sumint` statement (with the `ε`-mixture, DEGEN-VINE), the 30d Prop 6.1 gate and B2.2 hold, the recentered kernel of a
vine chain, seen as a function of the output times and of the boundary vector in the `sumint` convention, obeys

`‖K̃^U‖_{𝔛^{2η⁸,0,0}} ≤ (δ/2L^{d-γ})^{n₁} (cc_η+1) 3^{|U|} K₀ Σ ∏ L^{wE g} ∏ (Cfs · 2 B_ρ)`,

with `B_ρ = rowB P n_ρ g_ρ`, `n_ρ` the half order and `g_ρ` the incoherency index of the regular object of row `ρ`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.LGSpine WaveTurbulence.GammaLow.Famb.VineEstS2
  VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
open scoped ENNReal

/-- The `sumint` datum of Step 3. -/
noncomputable abbrev step3DΓ {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (badKind : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) : SumintDatum d :=
  sourceSumintDatumΓ hM9 B hG (step3WΓ hM9 B RD hG layer hLayer badKind qOut centre wBar)

end WaveTurbulence.GammaLow.Famb.VineEstS3

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Bounds
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.TreeClockOrder
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data` (sha256 3cad61d1f6834947…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Step 3 data: the weight record `W`, continuity and clock membership of the rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem step3W_okΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (badKind : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) :
    ConstraintsOKΓ hM9 B (step3WΓ hM9 B RD hG layer hLayer badKind qOut centre wBar) :=
  constraintsOK_unionΓ hM9 B _ rfl

section Rows
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS3

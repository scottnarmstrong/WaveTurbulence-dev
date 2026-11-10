/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.BadClause` (sha256 55a253ce4261cf8f…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # `BadClause` of the canonical bad kinds (TARGET Step 3, L1841-L1847)

`canonBadKind i = 0` if clause (a) holds for the vine `i` and `3` otherwise.  `badClause_canon`: with the case premise
`CoreVinesNoTwist`, `BadClause` holds for the `step3D` datum with this bad kind: clause (a) by definition, clause (d) by
`bad_d` (non-core and layer-ineligible vines satisfy (a), `aClause_typeII`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
variable (hLayer : IsLayering (RD.garden hG) layer)

open Classical in
/-- The bad kind of the vine `i`: `0` if clause (a) holds, `3` otherwise. -/
noncomputable def canonBadKindΓ (i : Fin (assemblyShapeΓ hM9 B).I) : Fin 4 :=
  if AClauseΓ hM9 B RD hG layer i then 0 else 3

theorem canonBadKind_casesΓ (i : Fin (assemblyShapeΓ hM9 B).I) :
    canonBadKindΓ hM9 B RD hG layer i = 0 ∨ canonBadKindΓ hM9 B RD hG layer i = 3 := by
  unfold canonBadKindΓ
  split_ifs <;> simp

end WaveTurbulence.GammaLow.Famb.VineEstS3

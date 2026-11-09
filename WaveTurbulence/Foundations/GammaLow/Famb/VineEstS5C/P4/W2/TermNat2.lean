/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BadEng
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClause
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.BadEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.TermNat1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat2` (sha256 b60279e75a0a451c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 12, step 1b): data of the native certificate -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The weight/clock record of a (modulated) term: the Step-3 record with the modulation `λ` at the first clock. -/
noncomputable def termWΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) :
    SumintWeightClockData (assemblyShapeΓ hM9 B) d :=
  { step3WΓ hM9 B RD hG layer hLayer bk qOut centre wBar with
    param := fun v => if v = (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩ : (assemblyShapeΓ hM9 B).TVar) then lam else 0 }

/-- The engine datum of a native term (no exceptional record): block kinds `canonBadKind`, constraints `consX .. ∅ ∅` (= native constraints with the
layer-order pairs), native exponents, `wN = 30 d - 1`, `wDec = 30 d`. -/
noncomputable abbrev natEngΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d)
    (wBar : Mom d) (lam : ℝ) : SumintPar.SumintDatum d :=
  engDatumΓ hM9 B hG (termWΓ hM9 B RD hG layer hLayer (canonBadKindΓ hM9 B RD hG layer) qOut centre wBar lam) (30 * d - 1) (30 * d)
    (canonBadKindΓ hM9 B RD hG layer) (consXΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅)
    (rowCoupleGΓ hM9 B RD hG layer hLayer) (rowTreeGΓ hM9 B RD hG layer hLayer)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2

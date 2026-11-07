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

/-! # P4-W2 (session 12, step 1b): data of the native certificate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The weight/clock record of a (modulated) term: the Step-3 record with the modulation `λ` at the first clock. -/
noncomputable def termW (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (bk : Fin (assemblyShape hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) :
    SumintWeightClockData (assemblyShape hM9 B) d :=
  { step3W hM9 B RD hG layer hLayer bk qOut centre wBar with
    param := fun v => if v = (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩ : (assemblyShape hM9 B).TVar) then lam else 0 }

/-- The size of the certificate: `traceConst² · pre · ∏ Rb` (`AmbW.pre` with the mass `mass`). -/
noncomputable def certBeta (P : WTParams) (D : SumintPar.SumintDatum P.d) (mass : ℝ) (Rb : Row D → ℝ≥0∞) : ℝ≥0∞ :=
  Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
    ((ccη P.η + 1) * ENNReal.ofReal (mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
      sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) * ∏ ρ, Rb ρ)

theorem certBeta_mono (P : WTParams) (D : SumintPar.SumintDatum P.d) (mass : ℝ) {Rb Rb' : Row D → ℝ≥0∞}
    (h : ∀ ρ, Rb ρ ≤ Rb' ρ) : certBeta P D mass Rb ≤ certBeta P D mass Rb' :=
  mul_le_mul' le_rfl (mul_le_mul' le_rfl (Finset.prod_le_prod' fun ρ _ => h ρ))

/-- The engine datum of a native term (no exceptional record): block kinds `canonBadKind`, constraints `consX .. ∅ ∅` (= native constraints with the
layer-order pairs), native exponents, `wN = 30 d - 1`, `wDec = 30 d`. -/
noncomputable abbrev natEng (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d)
    (wBar : Mom d) (lam : ℝ) : SumintPar.SumintDatum d :=
  engDatum hM9 B hG (termW hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) qOut centre wBar lam) (30 * d - 1) (30 * d)
    (canonBadKind hM9 B RD hG layer) (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅)
    (rowCoupleG hM9 B RD hG layer hLayer) (rowTreeG hM9 B RD hG layer hLayer)

end WaveTurbulence.VineEstS5C.P4.W2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.ScaledSumintMix
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.EngineAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.OutMod
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Bounds
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Modes
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Expand

/-! # The arity-3 engine with a character-mixture multiplier and a kind-2 phase (V5 Step 4d-A, item 2)

`clockedBoundMix3`: every weight row has three clocks.  The constant is `engineConst3` (the arity-3 analogue of
`engineConst`); `η ≤ 1/2` replaces `η ≤ 1`.  The kind-2 phase factor enters only through `Cph`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS
  Finset MeasureTheory
open scoped ENNReal

/-- **One mode.** -/
theorem mode_bound_mix3 {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I)
    (Mx : CharMix D.S P.d)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows3 D) (M : ClockedModes3 D (6 * P.η ^ 6))
    (m : Row D → Fin 3 → ℤ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => outFactor (modeFreq3 D cr.slot m) tt *
          exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) Mx hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  set D' : SumintPar.SumintDatum P.d := { D with param := fun v => D.param v + modeParam3 D cr.slot m v } with hD'
  have hAdm' : ∀ (p : D'.S.TVar → ℝ) (a : D'.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D'.S.VIdx → Mom P.d → ℂ), WeightBounds D' P.L P.γ P.η a b →
      ({ D' with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D :=
    fun p a b hb => hAdm p a b hb
  have hM' : D'.S.M ≤ P.N 1 ^ 4 := hM
  set w : Row D' → Mom P.d → Mom P.d → ℂ := fun ρ => M.c ρ (m ρ) with hw
  set s : Row D' → ℝ := fun ρ => M.S ρ (m ρ) with hs
  have hRB : RowBounds D' w s := by
    refine ⟨fun v r => ?_, fun v => ?_⟩
    · refine le_trans (le_iSup (fun r' => SNorm D.wN (rowOrder D (Sum.inl v)) (M.c (Sum.inl v) (m (Sum.inl v)) r')) r) ?_
      exact (ENNReal.ofReal_toReal (M.sn_ne_top hθfs (Sum.inl v) (m (Sum.inl v)))).symm.le
    · refine le_trans (le_iSup (fun r' => SNorm D.wN (rowOrder D (Sum.inr v)) (M.c (Sum.inr v) (m (Sum.inr v)) r')) 0) ?_
      exact (ENNReal.ofReal_toReal (M.sn_ne_top hθfs (Sum.inr v) (m (Sum.inr v)))).symm.le
  have hsc := scaledSumintMixAt_of hdb hL D' hI Mx hAdm' hM' w s (fun ρ => M.S_nonneg ρ _) hRB
  have hout := WaveTurbulence.VineEstS3.Eng.XNorm00Restr_outFactor_le (2 * P.η ^ 8) (modeFreq3 D cr.slot m) (outBox D)
    (outSet D P.L P.γ P.η)
    (fun tt E => exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) Mx hI P.L P.γ (2 * P.δ) P.η tt E)
  have hsc' : XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
      (fun tt E => exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) Mx hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (Mx.mass * sumintRHS P D') := hsc
  refine hout.trans ?_
  refine (mul_le_mul_right hsc' _).trans ?_
  have hη6 : 0 ≤ P.η ^ 6 := by positivity
  have hθa : (0 : ℝ) ≤ 2 * P.η ^ 8 := by positivity
  have hθa' : |2 * P.η ^ 8| = 2 * P.η ^ 8 := abs_of_nonneg hθa
  have hS0 : ∀ ρ, 0 ≤ M.S ρ (m ρ) := fun ρ => M.S_nonneg ρ _
  have hLp : ∀ ρ, 0 ≤ P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) := fun ρ => (Real.rpow_pos_of_pos hL _).le
  have hmp0 : 0 ≤ maxPar D' ^ (P.η ^ 6) := Real.rpow_nonneg (by rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le) _
  have hR0 : 0 ≤ sumintRHS0 P D := by
    unfold sumintRHS0
    have h1 : 0 ≤ P.C₁ * P.δ ^ (-(1 : ℝ) / 2) := mul_nonneg hC1 (Real.rpow_nonneg hδ.le _)
    exact mul_nonneg (mul_nonneg hC1 (pow_nonneg h1 _)) (Real.rpow_nonneg hL.le _)
  have hreal := mode_real_bound3 D hη0.le hη1 cr.slot m
  have hRHS : sumintRHS P D' = maxPar D' ^ (P.η ^ 6) * sumintRHS0 P D := sumintRHS_eq P D'
  have hprodS : ∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) =
      (∏ ρ, M.S ρ (m ρ)) * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) :=
    Finset.prod_mul_distrib
  have hprodM : ∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)) =
      (∏ ρ, modeBr3 D m ρ ^ (6 * P.η ^ 6)) * ∏ ρ, M.S ρ (m ρ) := Finset.prod_mul_distrib
  have hmbp : ∀ ρ, maxBracketPow (6 * P.η ^ 6) (half (m ρ)) = ENNReal.ofReal (modeBr3 D m ρ ^ (6 * P.η ^ 6)) := by
    intro ρ
    rw [NormBridgeScratch.maxBracketPow_eq_timeWeight]
    rfl
  have hX0 : ∀ ρ, 0 ≤ modeBr3 D m ρ ^ (6 * P.η ^ 6) := fun ρ =>
    Real.rpow_nonneg (le_trans zero_le_one (one_le_modeBr3 D m ρ)) _
  have hSprod0 : 0 ≤ ∏ ρ, M.S ρ (m ρ) := Finset.prod_nonneg fun ρ _ => hS0 ρ
  have hLprod0 : 0 ≤ ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) :=
    Finset.prod_nonneg fun ρ _ => hLp ρ
  have hXprod0 : 0 ≤ ∏ ρ, modeBr3 D m ρ ^ (6 * P.η ^ 6) := Finset.prod_nonneg fun ρ _ => hX0 ρ
  have hEc := engineConst3_nonneg P.η (Fintype.card (Row D))
  have hmP0 : 0 ≤ maxPar D ^ (P.η ^ 6) :=
    Real.rpow_nonneg (by rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le) _
  -- the real inequality
  have hrl0 : (2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
      (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        sumintRHS P D' ≤
      engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
        (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ))) := by
    rw [hRHS, hprodS, hprodM]
    have hD'eq : maxPar D' = maxPar { D with param := fun v => D.param v + modeParam3 D cr.slot m v } := rfl
    have hr2 := hreal
    have hnn : 0 ≤ sumintRHS0 P D * (∏ ρ, M.S ρ (m ρ)) * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) :=
      mul_nonneg (mul_nonneg hR0 hSprod0) hLprod0
    calc (2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
          ((∏ ρ, M.S ρ (m ρ)) * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
          (maxPar D' ^ (P.η ^ 6) * sumintRHS0 P D)
        = ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
            maxPar D' ^ (P.η ^ 6)) * (sumintRHS0 P D * (∏ ρ, M.S ρ (m ρ)) *
            ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) := by ring
      _ ≤ (engineConst3 P.η (Fintype.card (Row D)) *
          maxPar D ^ (P.η ^ 6) * ∏ ρ, modeBr3 D m ρ ^ (6 * P.η ^ 6)) * (sumintRHS0 P D * (∏ ρ, M.S ρ (m ρ)) *
            ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) := mul_le_mul_of_nonneg_right hr2 hnn
      _ = _ := by ring
  have hrl : (2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
      (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        (Mx.mass * sumintRHS P D') ≤
      Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ))) := by
    calc _ = Mx.mass * ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
          (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) * sumintRHS P D') := by ring
      _ ≤ Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
          (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)))) :=
        mul_le_mul_of_nonneg_left hrl0 Mx.mass_nonneg
      _ = _ := by ring
  have hRs : 0 ≤ sumintRHS P D' := by
    rw [hRHS]; exact mul_nonneg hmp0 hR0
  have htbn : 0 ≤ (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) :=
    Real.rpow_nonneg (timeBracket_pos _).le _
  have h2n : (0 : ℝ) ≤ 2 ^ (2 * P.η ^ 8) := by positivity
  have hPn : 0 ≤ ∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) :=
    Finset.prod_nonneg fun ρ _ => mul_nonneg (hS0 ρ) (hLp ρ)
  have eL : ENNReal.ofReal (2 ^ |2 * P.η ^ 8|) *
      timeWeight |2 * P.η ^ 8| (fun c => modeFreq3 D cr.slot m c / 2) *
      (ENNReal.ofReal (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (Mx.mass * sumintRHS P D')) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
        (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) * (Mx.mass * sumintRHS P D')) := by
    rw [hθa']
    unfold timeWeight
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h2n htbn) hPn), ENNReal.ofReal_mul (mul_nonneg h2n htbn),
      ENNReal.ofReal_mul h2n]
    ring
  have eR : ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) =
      ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg Mx.mass_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hEc hmP0) hR0) hLprod0)),
      ENNReal.ofReal_prod_of_nonneg (fun ρ _ => mul_nonneg (hX0 ρ) (hS0 ρ))]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [hmbp, ENNReal.ofReal_mul (hX0 ρ)]
  rw [eL, eR]
  exact ENNReal.ofReal_le_ofReal hrl


/-- **The engine with a multiplier, kind-2 phase allowed.** The unimodularity `badKind <> 2` is replaced by `3 eta <= 1`
(continuity) and a bound `Cph` of the norm of the phase on the time domain; the conclusion is that of `clockedBoundMix3`. -/
theorem clockedBoundMix3 {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows3 D) (M : ClockedModes3 D (6 * P.η ^ 6))
    (hser : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ r k,
      HasSum (fun m => M.c ρ m r k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) r k)) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx cr hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) * ∏ ρ, M.b ρ := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hθa : (0 : ℝ) ≤ 2 * P.η ^ 8 := by positivity
  have hN : P.d + 1 ≤ D.wDec := hreg
  have key : ∀ tt ∈ outBox D, ∀ E ∈ outSet D P.L P.γ P.η,
      HasSum (fun m : Row D → Fin 3 → ℤ => outFactor (modeFreq3 D cr.slot m) tt *
        exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) Mx hI P.L P.γ (2 * P.δ) P.η tt E) (clockedExprMul3 Mx cr hI P.L P.γ (2 * P.δ) P.η tt E) := by
    intro tt htt E hE
    exact (clockedExprMul3_hasSum_Cph Mx cr M.c (fun ρ m => M.S ρ m) (decayWt D D.wDec)
      (fun m v r r' k => M.c_indep v (m (Sum.inr v)) r r' k) hI P.L P.γ
      (2 * P.δ) P.η hη3 tt E Cph hCph0 (hCph tt htt) ((hser tt htt).mono fun τ hs ρ k => hs ρ (E 0 - E 1) k) (fun ρ m => M.S_nonneg ρ m)
      (fun ρ => M.summable_S hθfs ρ) (decayWt_nonneg D D.wDec) (fun ρ m r k => M.norm_le hθfs ρ m r k)
      (summable_decayWt D hL hN E))
  have hmink := WaveTurbulence.VineEstS3.Mink.XNorm00Restr_tsum_le (θ := 2 * P.η ^ 8) hθa (fun c => (D.qOut c : ℝ))
    (outBox_subset_cell D) (countable_outSet D P.L P.γ P.η)
    (fun m tt E => outFactor (modeFreq3 D cr.slot m) tt *
      exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) Mx hI P.L P.γ (2 * P.δ) P.η tt E)
    (fun tt E => clockedExprMul3 Mx cr hI P.L P.γ (2 * P.δ) P.η tt E) key
  rw [cc_translate] at hmink
  refine hmink.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  calc ∑' m : Row D → Fin 3 → ℤ, XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => outFactor (modeFreq3 D cr.slot m) tt *
          exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) Mx hI P.L P.γ (2 * P.δ) P.η tt E)
      ≤ ∑' m : Row D → Fin 3 → ℤ, ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) *
          maxPar D ^ (P.η ^ 6) * sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) :=
        ENNReal.tsum_le_tsum fun m => mode_bound_mix3 hdb hL hη0 hη1 hC1 hδ hI Mx hAdm hM cr M m
    _ = ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ∑' m : Row D → Fin 3 → ℤ, ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) *
          ENNReal.ofReal (M.S ρ (m ρ))) := ENNReal.tsum_mul_left
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        rw [WaveTurbulence.VineEstS3.Eng.ennreal_tsum_pi_prod (fun ρ (m' : Fin 3 → ℤ) => maxBracketPow (6 * P.η ^ 6) (half m') *
          ENNReal.ofReal (M.S ρ m'))]
        refine Finset.prod_le_prod fun ρ _ => ?_
        refine le_trans (le_of_eq (tsum_congr fun m' => ?_)) (M.fs_bound ρ)
        rw [show ENNReal.ofReal (M.S ρ m') = M.sn ρ m' from
          ENNReal.ofReal_toReal (M.sn_ne_top hθfs ρ m')]
        rfl



end WaveTurbulence.VineEstS3Par.Eng

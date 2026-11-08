/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.Sumint
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine

/-! # V5W-T T3: certificate-to-bound with an output-dependent multiplier (the tertiary risk, resolved)

`W2.TermCertW` stores the engine data `Z : AmbW A P D` (with a `CharMix` `Z.Mx`), the rows and the free-domain
dictionary; its consumers `W2.termBoundW`, `W2.habsW` use the mixture through per-output identities (`Mx.val L E`) and
ONE sup-over-outputs estimate, `Z.bound` (`allRows_bound → clockedBoundMix3 → scaledSumintMixAt_of Z.hdb`).  So the
path is separable from W2's construction: `termBoundWOut`/`habsWOut` destructure the certificate, multiply `Z.Mx` by
the output-dependent mixture `N` of an `EnginePullbackOut` (`OutCharMix.mulC`), reuse the per-output lemmas of main at
the frozen mixture, and replace `Z.bound` by `allRows_boundOut`, whose only new input is
`SumintMixParDoubledOutAt A P` (T2).

Copied by source from main 416902c8: `VineEstS5A/A3Engine.lean` (`mode_bound_mix3`, `clockedBoundMix3`),
`VineEstS5C/P4/AllRows.lean` (`allRows_bound`), `VineEstS5C/P4/W2/Free.lean` (`termFnR_leaf_eq`, `termBoundW`, `habsW`),
and V5W-A's `VineSpaceK/Engine.lean` (`addMix_pre` as `pre_mulC`); `EnginePullbackOut` from the S-V5W probe §3.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.V5WT

section A3
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS
  Finset MeasureTheory
open scoped ENNReal

/-- **One mode.** -/
theorem mode_bound_mix3Out {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledOutAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I)
    (Mo : OutCharMix D.S P.d)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows3 D) (M : ClockedModes3 D (6 * P.η ^ 6))
    (m : Row D → Fin 3 → ℤ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => outFactor (modeFreq3 D cr.slot m) tt *
          exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) (Mo.freeze E) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
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
  have hsc := scaledSumintMixOutAt_of hdb hL D' hI Mo hAdm' hM' w s (fun ρ => M.S_nonneg ρ _) hRB
  have hout := WaveTurbulence.VineEstS3.Eng.XNorm00Restr_outFactor_le (2 * P.η ^ 8) (modeFreq3 D cr.slot m) (outBox D)
    (outSet D P.L P.γ P.η)
    (fun tt E => exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) (Mo.freeze E) hI P.L P.γ (2 * P.δ) P.η tt E)
  have hsc' : XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
      (fun tt E => exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) (Mo.freeze E) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (Mo.mass * sumintRHS P D') := hsc
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
        (Mo.mass * sumintRHS P D') ≤
      Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ))) := by
    calc _ = Mo.mass * ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
          (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) * sumintRHS P D') := by ring
      _ ≤ Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
          (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)))) :=
        mul_le_mul_of_nonneg_left hrl0 Mo.mass_nonneg
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
        ENNReal.ofReal (Mo.mass * sumintRHS P D')) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq3 D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
        (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) * (Mo.mass * sumintRHS P D')) := by
    rw [hθa']
    unfold timeWeight
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h2n htbn) hPn), ENNReal.ofReal_mul (mul_nonneg h2n htbn),
      ENNReal.ofReal_mul h2n]
    ring
  have eR : ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) =
      ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        (∏ ρ, (modeBr3 D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg Mo.mass_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hEc hmP0) hR0) hLprod0)),
      ENNReal.ofReal_prod_of_nonneg (fun ρ _ => mul_nonneg (hX0 ρ) (hS0 ρ))]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [hmbp, ENNReal.ofReal_mul (hX0 ρ)]
  rw [eL, eR]
  exact ENNReal.ofReal_le_ofReal hrl


/-- **The engine with a multiplier, kind-2 phase allowed.** The unimodularity `badKind <> 2` is replaced by `3 eta <= 1`
(continuity) and a bound `Cph` of the norm of the phase on the time domain; the conclusion is that of `clockedBoundMix3`. -/
theorem clockedBoundMix3Out {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledOutAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mo : OutCharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows3 D) (M : ClockedModes3 D (6 * P.η ^ 6))
    (hser : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ r k,
      HasSum (fun m => M.c ρ m r k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) r k)) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 (Mo.freeze E) cr hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) * ∏ ρ, M.b ρ := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hθa : (0 : ℝ) ≤ 2 * P.η ^ 8 := by positivity
  have hN : P.d + 1 ≤ D.wDec := hreg
  have key : ∀ tt ∈ outBox D, ∀ E ∈ outSet D P.L P.γ P.η,
      HasSum (fun m : Row D → Fin 3 → ℤ => outFactor (modeFreq3 D cr.slot m) tt *
        exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) (Mo.freeze E) hI P.L P.γ (2 * P.δ) P.η tt E) (clockedExprMul3 (Mo.freeze E) cr hI P.L P.γ (2 * P.δ) P.η tt E) := by
    intro tt htt E hE
    exact (clockedExprMul3_hasSum_Cph (Mo.freeze E) cr M.c (fun ρ m => M.S ρ m) (decayWt D D.wDec)
      (fun m v r r' k => M.c_indep v (m (Sum.inr v)) r r' k) hI P.L P.γ
      (2 * P.δ) P.η hη3 tt E Cph hCph0 (hCph tt htt) ((hser tt htt).mono fun τ hs ρ k => hs ρ (E 0 - E 1) k) (fun ρ m => M.S_nonneg ρ m)
      (fun ρ => M.summable_S hθfs ρ) (decayWt_nonneg D D.wDec) (fun ρ m r k => M.norm_le hθfs ρ m r k)
      (summable_decayWt D hL hN E))
  have hmink := WaveTurbulence.VineEstS3.Mink.XNorm00Restr_tsum_le (θ := 2 * P.η ^ 8) hθa (fun c => (D.qOut c : ℝ))
    (outBox_subset_cell D) (countable_outSet D P.L P.γ P.η)
    (fun m tt E => outFactor (modeFreq3 D cr.slot m) tt *
      exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) (Mo.freeze E) hI P.L P.γ (2 * P.δ) P.η tt E)
    (fun tt E => clockedExprMul3 (Mo.freeze E) cr hI P.L P.γ (2 * P.δ) P.η tt E) key
  rw [cc_translate] at hmink
  refine hmink.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  calc ∑' m : Row D → Fin 3 → ℤ, XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => outFactor (modeFreq3 D cr.slot m) tt *
          exprMix (D := modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam3 D cr.slot m)) (Mo.freeze E) hI P.L P.γ (2 * P.δ) P.η tt E)
      ≤ ∑' m : Row D → Fin 3 → ℤ, ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) *
          maxPar D ^ (P.η ^ 6) * sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) :=
        ENNReal.tsum_le_tsum fun m => mode_bound_mix3Out hdb hL hη0 hη1 hC1 hδ hI Mo hAdm hM cr M m
    _ = ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
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


end A3

section AllRowsOut
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory
  WaveTurbulence.VineEstS5C.P4
open scoped ENNReal

/-- **The engine bound with every row given.** -/
theorem allRows_boundOut {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledOutAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mo : OutCharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (R : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ) (hAe : ∀ ρ, (R ρ).Ae hI) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 (Mo.freeze E) (allCR R) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mo.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) * ∏ ρ, (R ρ).b :=
  clockedBoundMix3Out hdb hL hη0 hη1 hC1 hδ hd1 hI Mo hη3 Cph hCph0 hCph hreg hAdm hM (allCR R) (allCM R)
    (allRows_hser R hI hAe)

end AllRowsOut

/-! ## The output-dependent engine pullback and its product with a plain one -/

section Pull
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract
  VineEstS2 VineEstS3 VineEstS4 TTree
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- `VineSpaceK.EnginePullback` with an output-dependent mixture (S-V5W probe §3). -/
def EnginePullbackOut (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (mass : ℝ) : Prop :=
  ∀ (n : ℕ) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hL : L ≠ 0),
  ∃ N : OutCharMix (assemblyShape hM9 B) d, N.mass ≤ mass ∧
    ∀ (β : Fin 4 → Fin d → ℤ) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      m (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) =
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x

/-- A plain engine pullback is an output-dependent one. -/
theorem enginePullbackOut_of (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m : (GNode G.tree → Fin d → ℤ) → ℂ} {mass : ℝ} (h : VineSpaceK.EnginePullback R L base m mass) :
    EnginePullbackOut R L base m mass := by
  intro n hM9 B hL
  obtain ⟨N, hN, he⟩ := h n hM9 B hL
  exact ⟨OutCharMix.ofCharMix N, hN, he⟩

/-- **Product of a plain and an output-dependent engine pullback** (masses multiply). -/
theorem enginePullbackOut_mul (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m₁ m₂ : (GNode G.tree → Fin d → ℤ) → ℂ} {mass₁ mass₂ : ℝ}
    (h₁ : VineSpaceK.EnginePullback R L base m₁ mass₁) (h₂ : EnginePullbackOut R L base m₂ mass₂) :
    EnginePullbackOut R L base (fun z => m₁ z * m₂ z) (mass₁ * mass₂) := by
  intro n hM9 B hL
  obtain ⟨N₁, hN₁, he₁⟩ := h₁ n hM9 B hL
  obtain ⟨N₂, hN₂, he₂⟩ := h₂ n hM9 B hL
  refine ⟨OutCharMix.mulC N₁ N₂, ?_, ?_⟩
  · rw [OutCharMix.mulC_mass]
    exact mul_le_mul hN₁ hN₂ N₂.mass_nonneg (N₁.mass_nonneg.trans hN₁)
  · intro β hβ x
    beta_reduce
    rw [OutCharMix.mulC_val, he₁ β hβ x, he₂ β hβ x]

theorem enginePullbackOut_congr (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m m' : (GNode G.tree → Fin d → ℤ) → ℂ} {mass : ℝ} (h : EnginePullbackOut R L base m mass) (he : m = m') :
    EnginePullbackOut R L base m' mass := he ▸ h

theorem enginePullbackOut_mono (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m : (GNode G.tree → Fin d → ℤ) → ℂ} {mass mass' : ℝ} (h : EnginePullbackOut R L base m mass)
    (hm : mass ≤ mass') : EnginePullbackOut R L base m mass' := by
  intro n hM9 B hL
  obtain ⟨N, hN, he⟩ := h n hM9 B hL
  exact ⟨N, hN.trans hm, he⟩

end Pull

/-! ## The certificate-to-bound step with an output-dependent multiplier (no W2 re-run) -/

section Cert
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine
  WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- `FreeDict` depends on the mixture only through its value at the boundary output. -/
theorem freeDict_val_congr (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx Mx' : CharMix (assemblyShape hM9 B) d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hv : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      Mx'.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x)
    (hD : FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr) :
    FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx' cr := by
  intro x
  filter_upwards [hD x] with τ hτ
  rw [hτ, hv x]

variable {p : ℕ} {kind : Bool} (B : CLChainAssembly G R n) (hG : G.IsPlain)
variable {A : ℝ} {P : WTParams}

/-- Copy of `W2.termFnR_leaf_eq` with the mixture depending on the boundary output (`Mxf E`). -/
theorem termFnR_leaf_eqOut (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : Lvl B)
    (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)} (n' : ℕ) (hM9 : VINEPARAM) (B' : CLChainAssembly G lv.region n')
    (W : SumintWeightClockData (assemblyShape hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B').TVar × (assemblyShape hM9 B').TVar)) (g g' : (assemblyShape hM9 B').VIdx → ℕ)
    (Z : AmbW A P (engDatum hM9 B' hG W wN wDec bk cons g g'))
    (Mxf : (Fin 4 → Mom P.d) → CharMix (assemblyShape hM9 B') P.d)
    (Rw : ∀ ρ : Row (engDatum hM9 B' hG W wN wDec bk cons g g'), RowData (engDatum hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0) (hbase : W.wBar = κ0.base)
    (hind : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → ψ (clExtendIndices lv.region κ.1) t u = ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) t) u)
    (hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt)
        ψ wN wDec bk cons g g' (Mxf (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))))
        (allCR Rw))
    (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode) (tt : Fin 3 → ℝ) (htt : tt ∈ Bx) (E : Fin 4 → Mom P.d)
    (hE : E ∈ outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) :
    termFnR B (G.sign lv.c.a.toNode) κ0 lv ψ s tt E =
      Lvl.cst B κ0 lv * clockedExprMul3 (Mxf E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) E := by
  subst hs
  set q := (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
  set tt' := WaveTurbulence.VineEstS3.leafT q (LeafPos B lv) (LeafNeg B lv) tt with htt'
  have h0 : tt 0 = tt' 0 := (WaveTurbulence.VineEstS3.leafT_zero q _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar ψ tt tt' h0
    (by by_cases h : LeafPos B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : LeafNeg B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) E)
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  have hfd := termFnR_eq_expr3_free hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ tt' ψ wN wDec bk cons g g'
    (Mxf (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)))) (allCR Rw)
    (hD tt htt β hβ hE)
  unfold termFnR termFn Lvl.cst
  rw [hκL, hκγ, hκδ, ← hbase, hlk.1]
  have hrf : recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) =
      recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt'
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) := by
    unfold recFac; rw [← h0]
  rw [hrf]
  exact hfd

/-- The engine prefactor of the product mixture. -/
theorem pre_mulC {D : SumintPar.SumintDatum P.d} (Z : AmbW A P D) (N : OutCharMix D.S P.d) :
    (ccη P.η + 1) * ENNReal.ofReal ((OutCharMix.mulC Z.Mx N).mass *
      (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) = ENNReal.ofReal N.mass * Z.pre := by
  unfold AmbW.pre
  rw [OutCharMix.mulC_mass]
  rw [mul_assoc, ENNReal.ofReal_mul Z.Mx.mass_nonneg,
    ENNReal.ofReal_mul N.mass_nonneg, ENNReal.ofReal_mul Z.Mx.mass_nonneg]
  ac_rfl

/-- `allRows_boundOut` for the product mixture of a certificate, with the certificate's prefactor. -/
theorem allRows_boundOut_mulC (hdbO : SumintMixParDoubledOutAt A P) {D : SumintPar.SumintDatum P.d} (Z : AmbW A P D)
    (N : OutCharMix D.S P.d) (Rw : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ) (hAe : ∀ ρ, (Rw ρ).Ae Z.hI) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
      (fun tt E => clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal N.mass * Z.pre * ∏ ρ, (Rw ρ).b := by
  have h := allRows_boundOut hdbO Z.hL Z.hη0 Z.hη1 Z.hC1 Z.hδ Z.hd1 Z.hI (OutCharMix.mulC Z.Mx N) Z.hη3 Z.Cph Z.hCph0
    Z.hCph Z.hreg Z.hAdm Z.hM Rw hAe
  rwa [pre_mulC Z N] at h

/-- The certified term multiplied by an output-dependent pullback: the leaf independence and the free dictionary of the
product mixture `mulC Z.Mx N` (frozen at each boundary output). -/
theorem termCertW_mulOut_data (κ0 : KPar P.d) (lv : Lvl B) (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)}
    (n' : ℕ) (hM9 : VINEPARAM) (B' : CLChainAssembly G lv.region n')
    (W : SumintWeightClockData (assemblyShape hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B').TVar × (assemblyShape hM9 B').TVar)) (g g' : (assemblyShape hM9 B').VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B') P.d)
    (Rw : ∀ ρ : Row (engDatum hM9 B' hG W wN wDec bk cons g g'), RowData (engDatum hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0)
    (hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt)
        ψ wN wDec bk cons g g' Mx (allCR Rw))
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (N : OutCharMix (assemblyShape hM9 B') P.d)
    (hN : ∀ (β : Fin 4 → Fin P.d → ℤ) (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      m (clExtendIndices lv.region ((clNormalizedChainEquiv hL B' W.wBar β hβ hM9).symm x).1) =
        N.val P.L (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) x) :
    ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt)
        (spatialMul m ψ) wN wDec bk cons g g'
        ((OutCharMix.mulC Mx N).freeze (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))))
        (allCR Rw) := by
  intro tt htt β hβ hE
  have h1 := freeDict_mul hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
    (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt)
    ψ m wN wDec bk cons g g' Mx
    (N.freeze (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)))) (allCR Rw)
    (hD tt htt β hβ hE) (fun x => hN β hβ x)
  exact freeDict_val_congr hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ _ _ wN wDec bk cons g g' _ _ (allCR Rw)
    (fun x => (OutCharMix.mulC_val_freeze Mx N P.L _ x).symm) h1

/-- **T3: the term bound from W2's certificate and an output-dependent pullback** (`W2.termBoundW` for
`spatialMul m ψ`, re-run on the destructured certificate with the product mixture; the only new analytic input is
`SumintMixParDoubledOutAt A P`).  Nothing of W2's construction is re-run. -/
theorem termBoundWOut (hdbO : SumintMixParDoubledOutAt A P) (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ)
    (hκδ : κ0.δ = P.δ) (lv : Lvl B) (σ s : ℤˣ) (hσ : σ = G.sign lv.c.a.toNode) (hs : s = σ) {Bx : Set (Fin 3 → ℝ)}
    {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (ψ : PsiT G P.d) (hC : TermCertW (A := A) B hG κ0 lv ψ Bx K β')
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) {mass : ℝ} (hpull : EnginePullbackOut lv.region P.L κ0.base m mass) :
    XNorm00Restr (2 * P.η ^ 8) Bx K (termFnR B σ κ0 lv (spatialMul m ψ) s) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        (ENNReal.ofReal mass * β') := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs hσ
  have hpullW : EnginePullbackOut lv.region P.L W.wBar m mass := by rw [hbase]; exact hpull
  obtain ⟨N, hNm, hNe⟩ := hpullW n' hM9 B' hL
  have hD' := termCertW_mulOut_data B hG κ0 lv ψ n' hM9 B' W wN wDec bk cons g g' Z.Mx Rw hL hD m N hNe
  have hind' : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β')
      (u : GBranch G.tree → ℝ), u lv.c.a = t 0 →
      spatialMul m ψ (clExtendIndices lv.region κ.1) t u = spatialMul m ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) t) u := by
    intro t β'' κ u hu
    simp only [VineSpaceK.spatialMul]
    rw [hind t β'' κ u hu]
  have hθ : (0 : ℝ) ≤ 2 * P.η ^ 8 := by have := Z.hη0; positivity
  have hcst : Lvl.cst B κ0 lv = (coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region := by
    unfold Lvl.cst; rw [hκL, hκγ, hκδ]
  set Ifun : (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun tt E =>
    Lvl.cst B κ0 lv * clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E with hIfun
  have h1 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
      (termFnR B (G.sign lv.c.a.toNode) κ0 lv (spatialMul m ψ) (G.sign lv.c.a.toNode)) ≤
      XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
          (LeafPos B lv) (LeafNeg B lv) tt) E) :=
    XNorm00Restr_mono_of_eq _ _ _ _ _ (fun tt htt E hE =>
      termFnR_leaf_eqOut B hG κ0 hκL hκγ hκδ lv (spatialMul m ψ) n' hM9 B' W wN wDec bk cons g g' Z
        (fun E => (OutCharMix.mulC Z.Mx N).freeze E) Rw hL hbase hind' hD' _ rfl tt htt E hE)
  have h2 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
          (LeafPos B lv) (LeafNeg B lv) tt) E) ≤
      XNorm00Restr (2 * P.η ^ 8) (boxQ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut)
        (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
          (LeafPos B lv) (LeafNeg B lv) tt) E) :=
    XNorm00Restr_mono_set _ hBx _ _
  have hI : ∀ E ∈ outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η,
      ContinuousOn (fun t => Ifun t E) (WaveTurbulence.VineEstS3.cubeSet (engDatum hM9 B' hG W wN wDec bk cons g g').qOut) :=
    fun E _ => continuousOn_const.mul (expr_continuousOn_cube Z.hL Z.hI ((OutCharMix.mulC Z.Mx N).freeze E) Z.hη3 Z.hη0 Z.Cph Z.hCph0 Z.hCph
      Z.hreg Rw hWs E)
  have h3 := XNorm00Restr_leafQ hθ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
    (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun
    (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
      (LeafPos B lv) (LeafNeg B lv) tt) E)
    (LeafPos B lv) (LeafNeg B lv) hI (fun t _ v _ => rfl)
  have h4 : XNorm00Restr (2 * P.η ^ 8) (boxQ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut)
      (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        XNorm00Restr (2 * P.η ^ 8) (outBox (engDatum hM9 B' hG W wN wDec bk cons g g'))
          (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
          (fun tt E => clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) := by
    rw [hcst] at hIfun
    have := WaveTurbulence.VineEstS3.Eng.XNorm00Restr_const_mul_le (2 * P.η ^ 8)
      (outBox (engDatum hM9 B' hG W wN wDec bk cons g g')) (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
      ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region)
      (fun tt E => clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E)
    simpa [hIfun, hcst, outBoxPar_eq] using this
  have h5 := allRows_boundOut_mulC hdbO Z N Rw hAe
  have h6 : ENNReal.ofReal N.mass * Z.pre * ∏ ρ, (Rw ρ).b ≤ ENNReal.ofReal mass * (Z.pre * ∏ ρ, (Rw ρ).b) := by
    rw [mul_assoc]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hNm) le_rfl
  calc _ ≤ _ := h1.trans (h2.trans h3)
    _ ≤ Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
        (‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
          (ENNReal.ofReal mass * (Z.pre * ∏ ρ, (Rw ρ).b))) :=
      mul_le_mul' le_rfl (h4.trans (mul_le_mul' le_rfl (h5.trans h6)))
    _ = ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        (ENNReal.ofReal mass * (Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
          (Z.pre * ∏ ρ, (Rw ρ).b))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hβ)

/-- **T3: absolute convergence of the term from the certificate and an output-dependent pullback** (`W2.habsW`). -/
theorem habsWOut (κ0 : KPar P.d) (hκL : κ0.L = P.L) (lv : Lvl B) (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode)
    {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (ψ : PsiT G P.d)
    (hC : TermCertW (A := A) B hG κ0 lv ψ Bx K β')
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) {mass : ℝ} (hpull : EnginePullbackOut lv.region P.L κ0.base m mass) :
    ∀ tt ∈ Bx, ∀ E ∈ K, LkAbs lv.region κ0.L κ0.base (spatialMul m ψ) tt (sumintBoundary s E) := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs
  have hpullW : EnginePullbackOut lv.region P.L W.wBar m mass := by rw [hbase]; exact hpull
  obtain ⟨N, _, hNe⟩ := hpullW n' hM9 B' hL
  have hD' := termCertW_mulOut_data B hG κ0 lv ψ n' hM9 B' W wN wDec bk cons g g' Z.Mx Rw hL hD m N hNe
  have hind' : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β')
      (u : GBranch G.tree → ℝ), u lv.c.a = t 0 →
      spatialMul m ψ (clExtendIndices lv.region κ.1) t u = spatialMul m ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) t) u := by
    intro t β'' κ u hu
    simp only [VineSpaceK.spatialMul]
    rw [hind t β'' κ u hu]
  intro tt htt E hE
  set tt' := WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt
    with htt'
  have hmem : tt' ∈ outBox (engDatum hM9 B' hG W wN wDec bk cons g g') :=
    WaveTurbulence.VineEstS5C.P4.W2.leafT_mem_boxQ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut _ _ (hBx htt)
  have hAbs := allRows_abs Z.hL Z.hη0 (assemblyShape_I_pos hM9 B') ((OutCharMix.mulC Z.Mx N).freeze E) Z.hη3 Z.Cph
    Z.hCph0 Z.hCph Z.hreg Rw hAe tt' hmem E hE
  obtain ⟨β, hβ', rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  rw [hκL, ← hbase]
  have h0 : tt 0 = tt' 0 :=
    (WaveTurbulence.VineEstS3.leafT_zero (engDatum hM9 B' hG W wN wDec bk cons g g').qOut _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar (spatialMul m ψ) tt tt' h0
    (by by_cases h : LeafPos B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : LeafNeg B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind' tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) (sumintBoundary (G.sign lv.c.a.toNode)
      (fun j => W.wBar + latticePoint P.L (β j))))
  refine hlk.2.mpr ?_
  exact lkAbs_of_exprAbs_free hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ' tt' (spatialMul m ψ) wN wDec bk cons g g' _
    (allCR Rw) (hD' tt htt β hβ' hE) hAbs

end Cert


end WaveTurbulence.Flower.V5WT

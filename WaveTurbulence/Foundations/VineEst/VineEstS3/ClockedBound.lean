/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedModes
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ModeBounds2
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EngineAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.OutMod

/-! # The engine: `sumint` for clock-dependent weights

The clocked `sumint` expression (weights depending on clocks through Fourier series on unit cells) obeys the
`sumint` bound with the weights' restriction norms `b ρ` in place of the normalised weight sizes.  It is
assembled from the mode expansion (`clockedExpr_hasSum`), the countable Minkowski inequality
(`XNorm00Restr_tsum_le`), the output modulation cost, the scaled `sumint` (`scaledSumintAt_of`) and the
per-mode weight (`mode_real_bound`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS2 Finset
  MeasureTheory
open scoped ENNReal

/-- The `η`- and `|Row|`-dependent constant of the per-mode weight. -/
noncomputable def engineConst (η : ℝ) (K : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) * ((2 : ℝ) ^ (2 * η ^ 8 + η ^ 6) * 4 ^ (η ^ 6)) ^ K

theorem engineConst_nonneg (η : ℝ) (K : ℕ) : 0 ≤ engineConst η K := by
  unfold engineConst; positivity


/-- **One mode.** -/
theorem mode_bound {A : ℝ} {P : WTParams} (hdb : SumintDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) {D : SumintDatum P.d} (hI : 0 < D.S.I)
    (cfs cs : Fin D.S.I → ℤˣ)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D) (M : ClockedModes D (6 * P.η ^ 6))
    (m : Row D → Fin 2 → ℤ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => outFactor (modeFreq D cr.slot m) tt *
          signedExpr (modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam D cr.slot m)) cfs cs hI P.L P.γ
            (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  set D' : SumintDatum P.d := { D with param := fun v => D.param v + modeParam D cr.slot m v } with hD'
  have hAdm' : ∀ (p : D'.S.TVar → ℝ) (a b : D'.S.VIdx → Mom P.d → ℂ), WeightBounds D' P.L P.γ P.η a b →
      ({ D' with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D :=
    fun p a b hb => hAdm p a b hb
  have hM' : D'.S.M ≤ P.N 1 ^ 4 := hM
  set w : Row D' → Mom P.d → ℂ := fun ρ => M.c ρ (m ρ) with hw
  set s : Row D' → ℝ := fun ρ => M.S ρ (m ρ) with hs
  have hRB : RowBounds D' w s := by
    refine ⟨fun v => ?_, fun v => ?_⟩
    · exact (ENNReal.ofReal_toReal (M.snorm_ne_top hθfs (Sum.inl v) (m (Sum.inl v)))).symm.le
    · exact (ENNReal.ofReal_toReal (M.snorm_ne_top hθfs (Sum.inr v) (m (Sum.inr v)))).symm.le
  have hsc := scaledSumintAt_of hdb hL D' hI cfs cs hAdm' hM' w s (fun ρ => M.S_nonneg ρ _) hRB
  have hout := XNorm00Restr_outFactor_le (2 * P.η ^ 8) (modeFreq D cr.slot m) (outBox D)
    (outSet D P.L P.γ P.η)
    (fun tt E => signedExpr (modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam D cr.slot m)) cfs cs hI P.L P.γ
      (2 * P.δ) P.η tt E)
  have hsc' : XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
      (fun tt E => signedExpr (modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam D cr.slot m)) cfs cs hI P.L P.γ
        (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (sumintRHS P D') := hsc
  refine hout.trans ?_
  refine (mul_le_mul_right hsc' _).trans ?_
  have hη6 : 0 ≤ P.η ^ 6 := by positivity
  have hθa : (0 : ℝ) ≤ 2 * P.η ^ 8 := by positivity
  have hθa' : |2 * P.η ^ 8| = 2 * P.η ^ 8 := abs_of_nonneg hθa
  have hS0 : ∀ ρ, 0 ≤ M.S ρ (m ρ) := fun ρ => M.S_nonneg ρ _
  have hLp : ∀ ρ, 0 ≤ P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) := fun ρ => (Real.rpow_pos_of_pos hL _).le
  have hmp0 : 0 ≤ maxPar D' ^ (P.η ^ 6) := Real.rpow_nonneg (by rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (Jb_pos _).le) _
  have hR0 : 0 ≤ sumintRHS0 P D := by
    unfold sumintRHS0
    have h1 : 0 ≤ P.C₁ * P.δ ^ (-(1 : ℝ) / 2) := mul_nonneg hC1 (Real.rpow_nonneg hδ.le _)
    exact mul_nonneg (mul_nonneg hC1 (pow_nonneg h1 _)) (Real.rpow_nonneg hL.le _)
  have hreal := mode_real_bound D hη0.le hη1 cr.slot m
  have hRHS : sumintRHS P D' = maxPar D' ^ (P.η ^ 6) * sumintRHS0 P D := sumintRHS_eq P D'
  have hprodS : ∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) =
      (∏ ρ, M.S ρ (m ρ)) * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) :=
    Finset.prod_mul_distrib
  have hprodM : ∏ ρ, (modeBr D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)) =
      (∏ ρ, modeBr D m ρ ^ (6 * P.η ^ 6)) * ∏ ρ, M.S ρ (m ρ) := Finset.prod_mul_distrib
  have hmbp : ∀ ρ, maxBracketPow (6 * P.η ^ 6) (half (m ρ)) = ENNReal.ofReal (modeBr D m ρ ^ (6 * P.η ^ 6)) := by
    intro ρ
    rw [NormBridgeScratch.maxBracketPow_eq_timeWeight]
    rfl
  have hX0 : ∀ ρ, 0 ≤ modeBr D m ρ ^ (6 * P.η ^ 6) := fun ρ =>
    Real.rpow_nonneg (le_trans zero_le_one (one_le_modeBr D m ρ)) _
  have hSprod0 : 0 ≤ ∏ ρ, M.S ρ (m ρ) := Finset.prod_nonneg fun ρ _ => hS0 ρ
  have hLprod0 : 0 ≤ ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) :=
    Finset.prod_nonneg fun ρ _ => hLp ρ
  have hXprod0 : 0 ≤ ∏ ρ, modeBr D m ρ ^ (6 * P.η ^ 6) := Finset.prod_nonneg fun ρ _ => hX0 ρ
  have hEc := engineConst_nonneg P.η (Fintype.card (Row D))
  have hmP0 : 0 ≤ maxPar D ^ (P.η ^ 6) :=
    Real.rpow_nonneg (by rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (Jb_pos _).le) _
  -- the real inequality
  have hrl : (2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
      (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) *
        sumintRHS P D' ≤
      engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
        (∏ ρ, (modeBr D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ))) := by
    rw [hRHS, hprodS, hprodM]
    have hD'eq : maxPar D' = maxPar { D with param := fun v => D.param v + modeParam D cr.slot m v } := rfl
    have hr2 := hreal
    unfold engineConst
    have key : (2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
        maxPar D' ^ (P.η ^ 6) ≤ ((2 : ℝ) ^ (2 * P.η ^ 8) * Real.sqrt 2 ^ (P.η ^ 6)) *
        ((2 : ℝ) ^ (2 * P.η ^ 8 + P.η ^ 6) * 4 ^ (P.η ^ 6)) ^ Fintype.card (Row D) *
        maxPar D ^ (P.η ^ 6) * ∏ ρ, modeBr D m ρ ^ (6 * P.η ^ 6) := hr2
    have hnn : 0 ≤ sumintRHS0 P D * (∏ ρ, M.S ρ (m ρ)) * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) :=
      mul_nonneg (mul_nonneg hR0 hSprod0) hLprod0
    calc (2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
          ((∏ ρ, M.S ρ (m ρ)) * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
          (maxPar D' ^ (P.η ^ 6) * sumintRHS0 P D)
        = ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
            maxPar D' ^ (P.η ^ 6)) * (sumintRHS0 P D * (∏ ρ, M.S ρ (m ρ)) *
            ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) := by ring
      _ ≤ (((2 : ℝ) ^ (2 * P.η ^ 8) * Real.sqrt 2 ^ (P.η ^ 6)) *
          ((2 : ℝ) ^ (2 * P.η ^ 8 + P.η ^ 6) * 4 ^ (P.η ^ 6)) ^ Fintype.card (Row D) *
          maxPar D ^ (P.η ^ 6) * ∏ ρ, modeBr D m ρ ^ (6 * P.η ^ 6)) * (sumintRHS0 P D * (∏ ρ, M.S ρ (m ρ)) *
            ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) := mul_le_mul_of_nonneg_right key hnn
      _ = _ := by ring
  have hRs : 0 ≤ sumintRHS P D' := by
    rw [hRHS]; exact mul_nonneg hmp0 hR0
  have htbn : 0 ≤ (timeBracket fun c => modeFreq D cr.slot m c / 2) ^ (2 * P.η ^ 8) :=
    Real.rpow_nonneg (timeBracket_pos _).le _
  have h2n : (0 : ℝ) ≤ 2 ^ (2 * P.η ^ 8) := by positivity
  have hPn : 0 ≤ ∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) :=
    Finset.prod_nonneg fun ρ _ => mul_nonneg (hS0 ρ) (hLp ρ)
  have eL : ENNReal.ofReal (2 ^ |2 * P.η ^ 8|) *
      timeWeight |2 * P.η ^ 8| (fun c => modeFreq D cr.slot m c / 2) *
      (ENNReal.ofReal (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (sumintRHS P D')) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * P.η ^ 8) * (timeBracket fun c => modeFreq D cr.slot m c / 2) ^ (2 * P.η ^ 8) *
        (∏ ρ, (M.S ρ (m ρ) * P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)))) * sumintRHS P D') := by
    rw [hθa']
    unfold timeWeight
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h2n htbn) hPn), ENNReal.ofReal_mul (mul_nonneg h2n htbn),
      ENNReal.ofReal_mul h2n]
    ring
  have eR : ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) =
      ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        (∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) *
        (∏ ρ, (modeBr D m ρ ^ (6 * P.η ^ 6) * M.S ρ (m ρ)))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hEc hmP0) hR0) hLprod0),
      ENNReal.ofReal_prod_of_nonneg (fun ρ _ => mul_nonneg (hX0 ρ) (hS0 ρ))]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [hmbp, ENNReal.ofReal_mul (hX0 ρ)]
  rw [eL, eR]
  exact ENNReal.ofReal_le_ofReal hrl


/-- **The engine.** -/
theorem clockedBound {A : ℝ} {P : WTParams} (hdb : SumintDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintDatum P.d} (hI : 0 < D.S.I) (cfs cs : Fin D.S.I → ℤˣ)
    (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D) (M : ClockedModes D (6 * P.η ^ 6))
    (hser : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ k,
      HasSum (fun m => M.c ρ m k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) k)) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExpr cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) * ∏ ρ, M.b ρ := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hθa : (0 : ℝ) ≤ 2 * P.η ^ 8 := by positivity
  have hN : P.d + 1 ≤ 30 * P.d := by omega
  have key : ∀ tt ∈ outBox D, ∀ E ∈ outSet D P.L P.γ P.η,
      HasSum (fun m : Row D → Fin 2 → ℤ => outFactor (modeFreq D cr.slot m) tt *
        signedExpr (modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam D cr.slot m)) cfs cs hI P.L P.γ
          (2 * P.δ) P.η tt E) (clockedExpr cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) := by
    intro tt htt E hE
    exact (clockedExpr_hasSum cr M.c (fun ρ m => M.S ρ m) (decayWt D (30 * P.d)) hno hbad cfs cs hI P.L P.γ
      (2 * P.δ) P.η tt E (hser tt htt) (fun ρ m => M.S_nonneg ρ m) (fun ρ => M.summable_S hθfs ρ)
      (decayWt_nonneg D (30 * P.d)) (fun ρ m k => M.norm_le hθfs ρ m k)
      (summable_decayWt D hL hN E)).1
  have hmink := Mink.XNorm00Restr_tsum_le (θ := 2 * P.η ^ 8) hθa (fun c => (D.qOut c : ℝ))
    (outBox_subset_cell D) (countable_outSet D P.L P.γ P.η)
    (fun m tt E => outFactor (modeFreq D cr.slot m) tt *
      signedExpr (modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam D cr.slot m)) cfs cs hI P.L P.γ
        (2 * P.δ) P.η tt E)
    (fun tt E => clockedExpr cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) key
  rw [cc_translate] at hmink
  refine hmink.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  calc ∑' m : Row D → Fin 2 → ℤ, XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => outFactor (modeFreq D cr.slot m) tt *
          signedExpr (modeDatum D (fun ρ => M.c ρ (m ρ)) (modeParam D cr.slot m)) cfs cs hI P.L P.γ
            (2 * P.δ) P.η tt E)
      ≤ ∑' m : Row D → Fin 2 → ℤ, ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) *
          maxPar D ^ (P.η ^ 6) * sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) *
        ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) * ENNReal.ofReal (M.S ρ (m ρ))) :=
        ENNReal.tsum_le_tsum fun m => mode_bound hdb hL hη0 hη1 hC1 hδ hI cfs cs hAdm hM cr M m
    _ = ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
          ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) *
        ∑' m : Row D → Fin 2 → ℤ, ∏ ρ, (maxBracketPow (6 * P.η ^ 6) (half (m ρ)) *
          ENNReal.ofReal (M.S ρ (m ρ))) := ENNReal.tsum_mul_left
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        rw [ennreal_tsum_pi_prod (fun ρ (m' : Fin 2 → ℤ) => maxBracketPow (6 * P.η ^ 6) (half m') *
          ENNReal.ofReal (M.S ρ m'))]
        refine Finset.prod_le_prod' fun ρ _ => ?_
        refine le_trans (le_of_eq (tsum_congr fun m' => ?_)) (M.fs_bound ρ)
        rw [show ENNReal.ofReal (M.S ρ m') = SNorm (30 * P.d) (rowOrder D ρ) (M.c ρ m') from
          ENNReal.ofReal_toReal (M.snorm_ne_top hθfs ρ m')]

end WaveTurbulence.VineEstS3.Eng

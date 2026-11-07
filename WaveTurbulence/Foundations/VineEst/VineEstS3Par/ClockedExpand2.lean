/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpand

/-! # The interchange theorem for a clocked `sumint` expression (engine step EXP) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- Pointwise: the clocked integrand is the sum of its mode terms. -/
theorem clockedIntegrand_hasSum (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (S : Row D → (Fin 2 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ)
    (hS : ∀ ρ, Summable (S ρ)) (hcS : ∀ ρ m r k, ‖c ρ m r k‖ ≤ S ρ m * Dec ρ k)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (τ : D.S.TVar → ℝ)
    (hser : ∀ ρ k, HasSum (fun m => c ρ m (E 0 - E 1) k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) k)) :
    HasSum (fun m : Row D → Fin 2 → ℤ => modeTerm cr c L γ δ η x E tt m τ)
      (clockedIntegrand cr L γ δ η x E tt τ) := by
  set a : Row D → (Fin 2 → ℤ) → ℂ := fun ρ m => c ρ m (E 0 - E 1) (rowMom D L x E ρ) * fsPhase m (cr.clock τ tt ρ) with ha
  have hsa : ∀ ρ, Summable fun m => ‖a ρ m‖ := by
    intro ρ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((hS ρ).mul_right (Dec ρ (rowMom D L x E ρ)))
    rw [ha]
    simp only [norm_mul, norm_fsPhase, mul_one]
    exact hcS _ _ _ _
  obtain ⟨-, hP⟩ := WaveTurbulence.VineEstS3.Eng.hasSum_pi_prod a hsa
  have hq : ∀ ρ, ∑' m, a ρ m = cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) (rowMom D L x E ρ) := fun ρ =>
    (hser ρ _).tsum_eq
  simp only [hq] at hP
  have := hP.mul_left (D.phase L γ δ η x (E 0 - E 1) (tt 0) τ)
  unfold clockedIntegrand
  convert this using 1
  funext m
  unfold modeTerm
  rw [Finset.prod_mul_distrib]


theorem integrand_modeTerm (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (m : Row D → Fin 2 → ℤ) (τ : D.S.TVar → ℝ) :
    modeTerm cr c L γ δ η x E tt m τ =
      outFactor (modeFreq D cr.slot m) tt * ((∏ ρ, c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)) *
        (D.phase L γ δ η x (E 0 - E 1) (tt 0) τ *
          paramFactor D (modeParam D cr.slot m) τ)) := by
  unfold modeTerm
  have := prod_fsPhase_clock D cr.slot m τ tt
  have h2 : ∏ ρ, fsPhase (m ρ) (cr.clock τ tt ρ) =
      paramFactor D (modeParam D cr.slot m) τ * outFactor (modeFreq D cr.slot m) tt := this
  rw [h2]
  ring

/-- **Interchange.** -/
theorem clockedExpr_hasSum (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (S : Row D → (Fin 2 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ)
    (hcL : ∀ (m : Row D → Fin 2 → ℤ) (v : D.S.VIdx) (r r' k : Mom d), c (Sum.inr v) (m (Sum.inr v)) r k = c (Sum.inr v) (m (Sum.inr v)) r' k)
    (hbad : ∀ i, D.badKind i ≠ 2)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d)
    (hser : ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ k,
      HasSum (fun m => c ρ m (E 0 - E 1) k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) k))
    (hS0 : ∀ ρ m, 0 ≤ S ρ m) (hS : ∀ ρ, Summable (S ρ)) (hDec0 : ∀ ρ k, 0 ≤ Dec ρ k)
    (hcS : ∀ ρ m r k, ‖c ρ m r k‖ ≤ S ρ m * Dec ρ k)
    (hDecX : Summable fun x : D.S.VIdx → (Fin d → ℤ) => ∏ ρ, Dec ρ (rowMom D L x E ρ)) :
    HasSum (fun m : Row D → Fin 2 → ℤ => outFactor (modeFreq D cr.slot m) tt *
        (modeDatum D (fun ρ => c ρ (m ρ)) (modeParam D cr.slot m)).expr hI L γ δ η tt E)
      (clockedExpr cr hI L γ δ η tt E) ∧
    ∀ m : Row D → Fin 2 → ℤ, ‖outFactor (modeFreq D cr.slot m) tt *
        (modeDatum D (fun ρ => c ρ (m ρ)) (modeParam D cr.slot m)).expr hI L γ δ η tt E‖ ≤
      (‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card) *
        ((∑' x, ∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ)) := by
  classical
  set T := D.timeDom hI (tt 0) (tt 1) (tt 2) with hTdef
  have hT : MeasurableSet T := measurableSet_timeDom D hI _ _ _
  set μ : Measure (D.S.TVar → ℝ) := volume.restrict T with hμ
  haveI : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (volume_timeDom_le D hI _ _ _) ENNReal.one_lt_top⟩
  have hμ1 : μ.real Set.univ ≤ 1 := by
    rw [Measure.real, hμ, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using volume_timeDom_le D hI _ _ _)
  set Bx : (D.S.VIdx → (Fin d → ℤ)) → ℝ := fun x => ∏ ρ, Dec ρ (rowMom D L x E ρ) with hBx
  set Bm : (Row D → Fin 2 → ℤ) → ℝ := fun m => ∏ ρ, S ρ (m ρ) with hBm
  have hBx0 : ∀ x, 0 ≤ Bx x := fun x => Finset.prod_nonneg fun ρ _ => hDec0 _ _
  have hBm0 : ∀ m, 0 ≤ Bm m := fun m => Finset.prod_nonneg fun ρ _ => hS0 _ _
  have hBmS : Summable Bm := by
    have := (WaveTurbulence.VineEstS3.Eng.hasSum_pi_prod (fun ρ (m : Fin 2 → ℤ) => S ρ m) (fun ρ => by
      simpa [Real.norm_of_nonneg (hS0 ρ _)] using hS ρ)).1
    refine this.congr fun m => ?_
    rw [norm_prod]
    exact Finset.prod_congr rfl fun ρ _ => Real.norm_of_nonneg (hS0 _ _)
  set G : (D.S.VIdx → (Fin d → ℤ)) → (Row D → Fin 2 → ℤ) → ℂ := fun x m =>
    ∫ τ, modeTerm cr c L γ δ η x E tt m τ ∂μ with hG
  have hmeas : ∀ x m, Continuous fun τ => modeTerm cr c L γ δ η x E tt m τ := by
    intro x m
    unfold modeTerm
    exact (continuous_phase D hbad L γ δ η x (E 0 - E 1) (tt 0)).mul
      (continuous_const.mul (continuous_finsetProd _ fun ρ _ => continuous_fsPhase_clock cr tt ρ _))
  have hbd : ∀ x m τ, ‖modeTerm cr c L γ δ η x E tt m τ‖ ≤ Bx x * Bm m :=
    fun x m τ => norm_modeTerm_le cr c S Dec hbad hS0 hDec0 hcS L γ δ η x E tt m τ
  have hint : ∀ x m, Integrable (fun τ => modeTerm cr c L γ δ η x E tt m τ) μ :=
    fun x m => Integrable.of_bound (hmeas x m).aestronglyMeasurable (Bx x * Bm m)
      (ae_of_all _ (hbd x m))
  have hGb : ∀ x m, ‖G x m‖ ≤ Bx x * Bm m := by
    intro x m
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ (hbd x m))).trans ?_
    exact mul_le_of_le_one_right (mul_nonneg (hBx0 x) (hBm0 m)) hμ1
  -- fibrewise sum over modes
  have hfib : ∀ x, HasSum (fun m => G x m)
      (∫ τ in T, clockedIntegrand cr L γ δ η x E tt τ) := by
    intro x
    have hsn : Summable fun m => ∫ τ, ‖modeTerm cr c L γ δ η x E tt m τ‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun τ => norm_nonneg _) (fun m => ?_)
        (hBmS.mul_left (Bx x))
      calc ∫ τ, ‖modeTerm cr c L γ δ η x E tt m τ‖ ∂μ
          ≤ ∫ _τ, Bx x * Bm m ∂μ :=
            integral_mono (hint x m).norm (integrable_const _) (fun τ => hbd x m τ)
        _ = μ.real Set.univ * (Bx x * Bm m) := by rw [integral_const]; simp [smul_eq_mul]
        _ ≤ Bx x * Bm m := mul_le_of_le_one_left (mul_nonneg (hBx0 x) (hBm0 m)) hμ1
    have h1 := hasSum_integral_of_summable_integral_norm (hint x) hsn
    have h2 : ∫ τ, ∑' m, modeTerm cr c L γ δ η x E tt m τ ∂μ =
        ∫ τ in T, clockedIntegrand cr L γ δ η x E tt τ := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hT] with τ hτ
      exact (clockedIntegrand_hasSum cr c S Dec hS hcS L γ δ η x E tt τ
        (fun ρ k => hser τ hτ ρ k)).tsum_eq
    rw [h2] at h1
    exact h1
  have hBxS : Summable Bx := hDecX
  have hprod : Summable fun p : (D.S.VIdx → (Fin d → ℤ)) × (Row D → Fin 2 → ℤ) => Bx p.1 * Bm p.2 :=
    summable_mul_of_summable_norm (f := Bx) (g := Bm)
      (hBxS.congr fun x => (Real.norm_of_nonneg (hBx0 x)).symm)
      (hBmS.congr fun m => (Real.norm_of_nonneg (hBm0 m)).symm)
  have hGs : Summable (Function.uncurry G) :=
    Summable.of_norm_bounded hprod (fun p => hGb p.1 p.2)
  have hcomm : ∑' x, ∑' m, G x m = ∑' m, ∑' x, G x m := hGs.tsum_comm.symm
  have hGeq : ∀ x m, G x m = outFactor (modeFreq D cr.slot m) tt * ((∏ ρ, c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)) *
      ∫ τ in T, D.phase L γ δ η x (E 0 - E 1) (tt 0) τ *
        paramFactor D (modeParam D cr.slot m) τ) := by
    intro x m
    simp only [hG, integrand_modeTerm]
    rw [integral_const_mul, integral_const_mul]
  set Fr : ℂ := ((‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) with hFr
  have hterm : ∀ m, Fr * ∑' x, G x m = outFactor (modeFreq D cr.slot m) tt *
      (modeDatum D (fun ρ => c ρ (m ρ)) (modeParam D cr.slot m)).expr hI L γ δ η tt E := by
    intro m
    rw [expr_modeDatum (D := D) (fun ρ => c ρ (m ρ)) (fun v r r' k => hcL m v r r' k), ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [hGeq x m]
    ring
  have hsum2 : Summable fun m => ∑' x, G x m := by
    have : Summable (Function.uncurry fun m x => G x m) :=
      (Equiv.prodComm _ _).summable_iff.1 hGs
    exact this.prod
  have hCe : clockedExpr cr hI L γ δ η tt E = Fr * ∑' x, ∑' m, G x m := by
    unfold clockedExpr
    refine congrArg (Fr * ·) (tsum_congr fun x => (hfib x).tsum_eq.symm)
  refine ⟨?_, fun m => ?_⟩
  · rw [hCe, hcomm]
    have := hsum2.hasSum.mul_left Fr
    simpa only [hterm] using this
  · rw [← hterm, norm_mul, hFr, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖∑' x, G x m‖ ≤ ∑' x, ‖G x m‖ := norm_tsum_le_tsum_norm
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => hGb x m) (hBxS.mul_right (Bm m)))
      _ ≤ ∑' x, Bx x * Bm m := (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => hGb x m)
          (hBxS.mul_right (Bm m))).tsum_le_tsum (fun x => hGb x m) (hBxS.mul_right (Bm m))
      _ = (∑' x, Bx x) * Bm m := tsum_mul_right

end WaveTurbulence.VineEstS3Par.Eng

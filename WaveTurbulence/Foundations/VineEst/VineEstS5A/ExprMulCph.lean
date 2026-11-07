/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.ClockedExprMul
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.PhasePhCph

/-! # The multiplied clocked expression with a kind-2 phase (V5 Step 4d-A, item 1)

`clockedExprMul_hasSum_Cph`: the mode interchange of `clockedExprMul_hasSum` without `badKind <> 2`; the integrand
is only bounded on the time domain (`kind2Factor <= Cph`), so every bound holds `volume.restrict timeDom`-a.e.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3Par.Eng Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

theorem norm_modeTerm_le_Cph (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (S : Row D → (Fin 2 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ)
    (hS0 : ∀ ρ m, 0 ≤ S ρ m) (hDec0 : ∀ ρ k, 0 ≤ Dec ρ k)
    (hcS : ∀ ρ m r k, ‖c ρ m r k‖ ≤ S ρ m * Dec ρ k)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ) (m : Row D → Fin 2 → ℤ) (τ : D.S.TVar → ℝ) (Cph : ℝ)
    (hτ : kind2Factor D η τ ≤ Cph) :
    ‖modeTerm cr c L γ δ η x E tt m τ‖ ≤
      (Cph * ∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ) := by
  unfold modeTerm
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_fsPhase, Finset.prod_const_one, mul_one]
  have h1 : ‖D.phase L γ δ η x (E 0 - E 1) (tt 0) τ‖ ≤ Cph := by rw [norm_phase_eq]; exact hτ
  have h2 : ∏ ρ, ‖c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)‖ ≤ ∏ ρ, (S ρ (m ρ) * Dec ρ (rowMom D L x E ρ)) :=
    by gcongr with ρ hρ; exact hcS _ _ _ _
  have h3 : ∏ ρ, (S ρ (m ρ) * Dec ρ (rowMom D L x E ρ)) =
      (∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ) := by
    rw [Finset.prod_mul_distrib, mul_comm]
  calc ‖D.phase L γ δ η x (E 0 - E 1) (tt 0) τ‖ *
        ∏ ρ, ‖c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)‖
      ≤ Cph * ((∏ ρ, Dec ρ (rowMom D L x E ρ)) * ∏ ρ, S ρ (m ρ)) :=
        mul_le_mul h1 (h2.trans_eq h3) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          ((norm_nonneg _).trans h1)
    _ = _ := by ring

/-- **Interchange** for the multiplied expression, kind-2 phase allowed: `hη3 : 3η ≤ 1` gives continuity and the
bound `hCph` on the time domain replaces unimodularity. -/
theorem clockedExprMul_hasSum_Cph (M : CharMix D.S d) (cr : ClockedRows D) (c : Row D → (Fin 2 → ℤ) → Mom d → Mom d → ℂ)
    (S : Row D → (Fin 2 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ)
    (hcL : ∀ (m : Row D → Fin 2 → ℤ) (v : D.S.VIdx) (r r' k : Mom d), c (Sum.inr v) (m (Sum.inr v)) r k = c (Sum.inr v) (m (Sum.inr v)) r' k)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (hη3 : 3 * η ≤ 1) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D η τ ≤ Cph)
    (hser : ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ k,
      HasSum (fun m => c ρ m (E 0 - E 1) k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) k))
    (hS0 : ∀ ρ m, 0 ≤ S ρ m) (hS : ∀ ρ, Summable (S ρ)) (hDec0 : ∀ ρ k, 0 ≤ Dec ρ k)
    (hcS : ∀ ρ m r k, ‖c ρ m r k‖ ≤ S ρ m * Dec ρ k)
    (hDecX : Summable fun x : D.S.VIdx → (Fin d → ℤ) => ∏ ρ, Dec ρ (rowMom D L x E ρ)) :
    HasSum (fun m : Row D → Fin 2 → ℤ => outFactor (modeFreq D cr.slot m) tt *
        exprMix (D := modeDatum D (fun ρ => c ρ (m ρ)) (modeParam D cr.slot m)) M
          hI L γ δ η tt E)
      (clockedExprMul M cr hI L γ δ η tt E) := by
  classical
  set T := D.timeDom hI (tt 0) (tt 1) (tt 2) with hTdef
  have hT : MeasurableSet T := SumintPar.measurableSet_timeDom D hI _ _ _
  set μ : Measure (D.S.TVar → ℝ) := volume.restrict T with hμ
  haveI : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (volume_timeDom_le D hI _ _ _) ENNReal.one_lt_top⟩
  have hμ1 : μ.real Set.univ ≤ 1 := by
    rw [Measure.real, hμ, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using volume_timeDom_le D hI _ _ _)
  set Bx : (D.S.VIdx → (Fin d → ℤ)) → ℝ := fun x => Cph * ∏ ρ, Dec ρ (rowMom D L x E ρ) with hBx
  set Bm : (Row D → Fin 2 → ℤ) → ℝ := fun m => ∏ ρ, S ρ (m ρ) with hBm
  have hBx0 : ∀ x, 0 ≤ Bx x := fun x => mul_nonneg hCph0 (Finset.prod_nonneg fun ρ _ => hDec0 _ _)
  have hBm0 : ∀ m, 0 ≤ Bm m := fun m => Finset.prod_nonneg fun ρ _ => hS0 _ _
  have hBmS : Summable Bm := by
    have := (WaveTurbulence.VineEstS3.Eng.hasSum_pi_prod (fun ρ (m : Fin 2 → ℤ) => S ρ m) (fun ρ => by
      simpa [Real.norm_of_nonneg (hS0 ρ _)] using hS ρ)).1
    refine this.congr fun m => ?_
    rw [norm_prod]
    exact Finset.prod_congr rfl fun ρ _ => Real.norm_of_nonneg (hS0 _ _)
  set G0 : (D.S.VIdx → (Fin d → ℤ)) → (Row D → Fin 2 → ℤ) → ℂ := fun x m =>
    ∫ τ, modeTerm cr c L γ δ η x E tt m τ ∂μ with hG0
  set G : (D.S.VIdx → (Fin d → ℤ)) → (Row D → Fin 2 → ℤ) → ℂ := fun x m => M.val L E x * G0 x m with hG
  have hmeas : ∀ x m, Continuous fun τ => modeTerm cr c L γ δ η x E tt m τ := by
    intro x m
    unfold modeTerm
    exact (continuous_phase_of_le D L γ δ η hη3 x (E 0 - E 1) (tt 0)).mul
      (continuous_const.mul (continuous_finsetProd _ fun ρ _ => continuous_fsPhase_clock cr tt ρ _))
  have hbd0 : ∀ x m, ∀ τ ∈ T, ‖modeTerm cr c L γ δ η x E tt m τ‖ ≤ Bx x * Bm m :=
    fun x m τ hτ => norm_modeTerm_le_Cph cr c S Dec hS0 hDec0 hcS L γ δ η x E tt m τ Cph (hCph τ hτ)
  have hbd : ∀ x m, ∀ᵐ τ ∂μ, ‖modeTerm cr c L γ δ η x E tt m τ‖ ≤ Bx x * Bm m := fun x m => by
    filter_upwards [ae_restrict_mem hT] with τ hτ using hbd0 x m τ hτ
  have hint : ∀ x m, Integrable (fun τ => modeTerm cr c L γ δ η x E tt m τ) μ :=
    fun x m => Integrable.of_bound (hmeas x m).aestronglyMeasurable (Bx x * Bm m)
      (hbd x m)
  have hG0b : ∀ x m, ‖G0 x m‖ ≤ Bx x * Bm m := by
    intro x m
    refine (norm_integral_le_of_norm_le_const (hbd x m)).trans ?_
    exact mul_le_of_le_one_right (mul_nonneg (hBx0 x) (hBm0 m)) hμ1
  have hGb : ∀ x m, ‖G x m‖ ≤ (M.mass * Bx x) * Bm m := by
    intro x m
    rw [hG]; simp only [norm_mul]
    calc ‖M.val L E x‖ * ‖G0 x m‖ ≤ M.mass * (Bx x * Bm m) :=
          mul_le_mul (M.norm_val_le L E x) (hG0b x m) (norm_nonneg _) M.mass_nonneg
      _ = _ := by ring
  have hfib0 : ∀ x, HasSum (fun m => G0 x m)
      (∫ τ in T, clockedIntegrand cr L γ δ η x E tt τ) := by
    intro x
    have hsn : Summable fun m => ∫ τ, ‖modeTerm cr c L γ δ η x E tt m τ‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun τ => norm_nonneg _) (fun m => ?_)
        (hBmS.mul_left (Bx x))
      calc ∫ τ, ‖modeTerm cr c L γ δ η x E tt m τ‖ ∂μ
          ≤ ∫ _τ, Bx x * Bm m ∂μ :=
            integral_mono_ae (hint x m).norm (integrable_const _) (hbd x m)
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
  have hfib : ∀ x, HasSum (fun m => G x m)
      (M.val L E x * ∫ τ in T, clockedIntegrand cr L γ δ η x E tt τ) :=
    fun x => (hfib0 x).mul_left _
  have hBxS : Summable Bx := hDecX.mul_left Cph
  have hprod : Summable fun p : (D.S.VIdx → (Fin d → ℤ)) × (Row D → Fin 2 → ℤ) =>
      (M.mass * Bx p.1) * Bm p.2 :=
    summable_mul_of_summable_norm (f := fun x => M.mass * Bx x) (g := Bm)
      ((hBxS.mul_left M.mass).congr fun x => (Real.norm_of_nonneg (mul_nonneg M.mass_nonneg (hBx0 x))).symm)
      (hBmS.congr fun m => (Real.norm_of_nonneg (hBm0 m)).symm)
  have hGs : Summable (Function.uncurry G) :=
    Summable.of_norm_bounded hprod (fun p => hGb p.1 p.2)
  have hcomm : ∑' x, ∑' m, G x m = ∑' m, ∑' x, G x m := hGs.tsum_comm.symm
  have hGeq : ∀ x m, G x m = outFactor (modeFreq D cr.slot m) tt *
      (M.val L E x * ((∏ ρ, c ρ (m ρ) (E 0 - E 1) (rowMom D L x E ρ)) *
      ∫ τ in T, D.phase L γ δ η x (E 0 - E 1) (tt 0) τ *
        paramFactor D (modeParam D cr.slot m) τ)) := by
    intro x m
    simp only [hG, hG0, integrand_modeTerm]
    rw [integral_const_mul, integral_const_mul]
    ring
  set Fr : ℂ := ((‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) with hFr
  have hterm : ∀ m, Fr * ∑' x, G x m = outFactor (modeFreq D cr.slot m) tt *
      exprMix (D := modeDatum D (fun ρ => c ρ (m ρ)) (modeParam D cr.slot m)) M hI L γ δ η tt E := by
    intro m
    rw [exprMix_modeDatum M (fun ρ => c ρ (m ρ)) (fun v r r' k => hcL m v r r' k), ← tsum_mul_left, ← tsum_mul_left,
      ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [hGeq x m]
    ring
  have hsum2 : Summable fun m => ∑' x, G x m := by
    have : Summable (Function.uncurry fun m x => G x m) :=
      (Equiv.prodComm _ _).summable_iff.1 hGs
    exact this.prod
  have hCe : clockedExprMul M cr hI L γ δ η tt E = Fr * ∑' x, ∑' m, G x m := by
    unfold clockedExprMul
    exact congrArg (Fr * ·) (tsum_congr fun x => (hfib x).tsum_eq.symm)
  rw [hCe, hcomm]
  have := hsum2.hasSum.mul_left Fr
  simpa only [hterm] using this

end WaveTurbulence.VineEstS5A

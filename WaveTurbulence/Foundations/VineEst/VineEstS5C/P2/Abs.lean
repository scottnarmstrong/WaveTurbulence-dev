/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Expand

/-! # P2: absolute convergence of the clocked expression (step 6, the Fubini interchange)

`clockedExprMul3_abs`: under the hypotheses of `clockedExprMul3_hasSum_Cph`, for every lattice index `x` the integrand
`clockedIntegrand3 ... x` is integrable on the time domain and `x ↦ M.val * ∫ ...` is summable (what linearity of the
expression over a finite sum of row families needs; the proof is the interchange proof of `A3Expand`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS
  Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

theorem clockedExprMul3_abs (M : CharMix D.S d) (cr : ClockedRows3 D) (c : Row D → (Fin 3 → ℤ) → Mom d → Mom d → ℂ)
    (S : Row D → (Fin 3 → ℤ) → ℝ) (Dec : Row D → Mom d → ℝ)
    (hcL : ∀ (m : Row D → Fin 3 → ℤ) (v : D.S.VIdx) (r r' k : Mom d), c (Sum.inr v) (m (Sum.inr v)) r k = c (Sum.inr v) (m (Sum.inr v)) r' k)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (hη3 : 3 * η ≤ 1) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D η τ ≤ Cph)
    (hser : ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ k,
      HasSum (fun m => c ρ m (E 0 - E 1) k * fsPhase m (cr.clock τ tt ρ)) (cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) k))
    (hS0 : ∀ ρ m, 0 ≤ S ρ m) (hS : ∀ ρ, Summable (S ρ)) (hDec0 : ∀ ρ k, 0 ≤ Dec ρ k)
    (hcS : ∀ ρ m r k, ‖c ρ m r k‖ ≤ S ρ m * Dec ρ k)
    (hDecX : Summable fun x : D.S.VIdx → (Fin d → ℤ) => ∏ ρ, Dec ρ (rowMom D L x E ρ)) :
    (∀ x : D.S.VIdx → (Fin d → ℤ), Integrable (fun τ => clockedIntegrand3 cr L γ δ η x E tt τ)
        (volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2)))) ∧
      Summable fun x : D.S.VIdx → (Fin d → ℤ) => M.val L E x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
        clockedIntegrand3 cr L γ δ η x E tt τ := by
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
  set Bm : (Row D → Fin 3 → ℤ) → ℝ := fun m => ∏ ρ, S ρ (m ρ) with hBm
  have hBx0 : ∀ x, 0 ≤ Bx x := fun x => mul_nonneg hCph0 (Finset.prod_nonneg fun ρ _ => hDec0 _ _)
  have hBm0 : ∀ m, 0 ≤ Bm m := fun m => Finset.prod_nonneg fun ρ _ => hS0 _ _
  have hBmS : Summable Bm := by
    have := (WaveTurbulence.VineEstS3.Eng.hasSum_pi_prod (fun ρ (m : Fin 3 → ℤ) => S ρ m) (fun ρ => by
      simpa [Real.norm_of_nonneg (hS0 ρ _)] using hS ρ)).1
    refine this.congr fun m => ?_
    rw [norm_prod]
    exact Finset.prod_congr rfl fun ρ _ => Real.norm_of_nonneg (hS0 _ _)
  set G0 : (D.S.VIdx → (Fin d → ℤ)) → (Row D → Fin 3 → ℤ) → ℂ := fun x m =>
    ∫ τ, modeTerm3 cr c L γ δ η x E tt m τ ∂μ with hG0
  set G : (D.S.VIdx → (Fin d → ℤ)) → (Row D → Fin 3 → ℤ) → ℂ := fun x m => M.val L E x * G0 x m with hG
  have hmeas : ∀ x m, Continuous fun τ => modeTerm3 cr c L γ δ η x E tt m τ := by
    intro x m
    unfold modeTerm3
    exact (continuous_phase_of_le D L γ δ η hη3 x (E 0 - E 1) (tt 0)).mul
      (continuous_const.mul (continuous_finsetProd _ fun ρ _ => continuous_fsPhase_clock3 cr tt ρ _))
  have hbd0 : ∀ x m, ∀ τ ∈ T, ‖modeTerm3 cr c L γ δ η x E tt m τ‖ ≤ Bx x * Bm m :=
    fun x m τ hτ => norm_modeTerm_le_Cph3 cr c S Dec hS0 hDec0 hcS L γ δ η x E tt m τ Cph (hCph τ hτ)
  have hbd : ∀ x m, ∀ᵐ τ ∂μ, ‖modeTerm3 cr c L γ δ η x E tt m τ‖ ≤ Bx x * Bm m := fun x m => by
    filter_upwards [ae_restrict_mem hT] with τ hτ using hbd0 x m τ hτ
  have hint : ∀ x m, Integrable (fun τ => modeTerm3 cr c L γ δ η x E tt m τ) μ :=
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
      (∫ τ in T, clockedIntegrand3 cr L γ δ η x E tt τ) := by
    intro x
    have hsn : Summable fun m => ∫ τ, ‖modeTerm3 cr c L γ δ η x E tt m τ‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun τ => norm_nonneg _) (fun m => ?_)
        (hBmS.mul_left (Bx x))
      calc ∫ τ, ‖modeTerm3 cr c L γ δ η x E tt m τ‖ ∂μ
          ≤ ∫ _τ, Bx x * Bm m ∂μ :=
            integral_mono_ae (hint x m).norm (integrable_const _) (hbd x m)
        _ = μ.real Set.univ * (Bx x * Bm m) := by rw [integral_const]; simp [smul_eq_mul]
        _ ≤ Bx x * Bm m := mul_le_of_le_one_left (mul_nonneg (hBx0 x) (hBm0 m)) hμ1
    have h1 := hasSum_integral_of_summable_integral_norm (hint x) hsn
    have h2 : ∫ τ, ∑' m, modeTerm3 cr c L γ δ η x E tt m τ ∂μ =
        ∫ τ in T, clockedIntegrand3 cr L γ δ η x E tt τ := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hT, hser] with τ hτ hs
      exact (clockedIntegrand_hasSum3 cr c S Dec hS hcS L γ δ η x E tt τ
        (fun ρ k => hs ρ k)).tsum_eq
    rw [h2] at h1
    exact h1
  have hfib : ∀ x, HasSum (fun m => G x m)
      (M.val L E x * ∫ τ in T, clockedIntegrand3 cr L γ δ η x E tt τ) :=
    fun x => (hfib0 x).mul_left _
  have hBxS : Summable Bx := hDecX.mul_left Cph
  have hprod : Summable fun p : (D.S.VIdx → (Fin d → ℤ)) × (Row D → Fin 3 → ℤ) =>
      (M.mass * Bx p.1) * Bm p.2 :=
    summable_mul_of_summable_norm (f := fun x => M.mass * Bx x) (g := Bm)
      ((hBxS.mul_left M.mass).congr fun x => (Real.norm_of_nonneg (mul_nonneg M.mass_nonneg (hBx0 x))).symm)
      (hBmS.congr fun m => (Real.norm_of_nonneg (hBm0 m)).symm)
  have hGs : Summable (Function.uncurry G) :=
    Summable.of_norm_bounded hprod (fun p => hGb p.1 p.2)
  refine ⟨fun x => ?_, hGs.prod.congr fun x => (hfib x).tsum_eq⟩
  have hcOn : ContinuousOn (fun τ => ∑' m, modeTerm3 cr c L γ δ η x E tt m τ) T :=
    continuousOn_tsum (fun m => (hmeas x m).continuousOn) ((hBmS.mul_left (Bx x))) (fun m τ hτ => hbd0 x m τ hτ)
  have hae : (fun τ => clockedIntegrand3 cr L γ δ η x E tt τ) =ᵐ[μ] fun τ => ∑' m, modeTerm3 cr c L γ δ η x E tt m τ := by
    filter_upwards [ae_restrict_mem hT, hser] with τ hτ hs
    exact (clockedIntegrand_hasSum3 cr c S Dec hS hcS L γ δ η x E tt τ (fun ρ k => hs ρ k)).tsum_eq.symm
  have hbnd : ∀ᵐ τ ∂μ, ‖∑' m, modeTerm3 cr c L γ δ η x E tt m τ‖ ≤ Bx x * ∑' m, Bm m := by
    filter_upwards [ae_restrict_mem hT] with τ hτ
    have := tsum_of_norm_bounded ((hBmS.mul_left (Bx x)).hasSum) (fun m => hbd0 x m τ hτ)
    rwa [tsum_mul_left] at this
  exact (Integrable.of_bound (hcOn.aestronglyMeasurable hT) _ hbnd).congr hae.symm

end WaveTurbulence.VineEstS3Par.Eng

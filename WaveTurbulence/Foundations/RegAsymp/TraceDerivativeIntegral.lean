/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TraceDerivative
public import WaveTurbulence.Foundations.ClassJR.MCGR

/-! # A dimension-free integrated derivative bound for a one-energy trace

This is the coefficient trace needed for the Wick zero-coordinate correction.
Only orders k and k+1 of the original source symbol occur.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ContDiff ENNReal

/-- Agreement with the landed product-measure insertion convention. -/
theorem optE_eq_optionInsert {ι : Type} [Fintype ι] (β : ι → ℝ) (r : ℝ) :
    optE β r = optionInsert r β := by
  ext i
  cases i <;> rfl

/-- Smoothness of each full derivative tensor along the frozen coordinate line. -/
theorem contDiff_tensor_optionInsert {ι Γ : Type} [Fintype ι] [DecidableEq ι]
    {C : (Option ι → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) (β : ι → ℝ) :
    ContDiff ℝ 1 (fun r => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (optionInsert r β))) := by
  have hΦ : ContDiff ℝ ∞ (iteratedFDeriv ℝ k (lift1 C lam)) :=
    (contDiff_lift1 hs).iteratedFDeriv_right (by exact_mod_cast le_top)
  have hp : ContDiff ℝ ∞ (fun r : ℝ => toLp 1 (optionInsert r β)) := by
    simp_rw [optionInsert_toLp_eq]
    fun_prop
  exact (hΦ.comp hp).of_le (by exact_mod_cast le_top)

/-- At fixed λ, tracing one coordinate costs just one full derivative,
with constant1 independent of the number of variables and derivative order. -/
theorem lintegral_dnorm_traceSymbol_le {ι Γ : Type} [Fintype ι]
    {C : (Option ι → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) :
    (∫⁻ β : ι → ℝ, dnorm k (traceSymbol C) β lam) ≤
      (∫⁻ α : Option ι → ℝ, dnorm k C α lam)+
        (∫⁻ α : Option ι → ℝ, dnorm (k+1) C α lam) := by
  classical
  have hp (β : ι → ℝ) : dnorm k (traceSymbol C) β lam ≤
      ∫⁻ r : ℝ, (dnorm k C (optE β r) lam+dnorm (k+1) C (optE β r) lam) := by
    apply (dnorm_traceSymbol_le hs k β).trans
    have hh := enorm_le_lintegral_Icc (contDiff_tensor_optionInsert hs k β) (0:ℝ)
    apply hh.trans
    apply (setLIntegral_le_lintegral _ _).trans
    apply lintegral_mono
    intro r
    dsimp only
    rw [optE_eq_optionInsert]
    change ‖iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (optionInsert r β))‖ₑ +
      ‖deriv (fun s => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (optionInsert s β))) r‖ₑ ≤
        dnorm k C (optionInsert r β) lam+dnorm (k+1) C (optionInsert r β) lam
    apply add_le_add le_rfl
    change ‖deriv (fun s => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (optionInsert s β))) r‖ₑ ≤
      ‖iteratedFDeriv ℝ (k+1) (lift1 C lam) (toLp 1 (optionInsert r β))‖ₑ
    exact enorm_le_iff_norm_le.mpr (norm_deriv_tensor_optionInsert_le hs k β r)
  have hm := ((continuous_dnorm hs k).measurable).add ((continuous_dnorm hs (k+1)).measurable)
  calc
    _ ≤ ∫⁻ β : ι → ℝ, ∫⁻ r : ℝ,
      (dnorm k C (optE β r) lam+dnorm (k+1) C (optE β r) lam) := lintegral_mono hp
    _ = ∫⁻ α : Option ι → ℝ, (dnorm k C α lam+dnorm (k+1) C α lam) :=
      (lintegral_optionPi hm).symm
    _ = _ := lintegral_add_left (continuous_dnorm hs k).measurable _

end WaveTurbulence.RegAsymp

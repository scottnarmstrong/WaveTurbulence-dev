/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentRemainderInputBounds
public import WaveTurbulence.Foundations.Spine.LowProfilePrefix
/-! Uniform original coherent inputs from compact-time WKE bounds and the source remainder. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem coherent_input_low_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hδ : 0 ≤ P.δ) (htime : P.τstar = (P.D : ℝ) * P.δ)
    (hφ : LowProfileAt P) (hC₁ : 1 ≤ P.C₁)
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) :
    SNormR (40 * P.d) (40 * P.d) (inputsF P R p) ≤ ENNReal.ofReal P.C₁ := by
  have hΛ := forty_dim_le_Lambda P hd hp.le
  have hh := inputsF_SNormR_bound P hd hL hp hΛ hΛ R hR (P.C₁ - 1) (by linarith) (by
    intro r hr
    apply hφ
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg r), ?_⟩
    rw [htime]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show (r : ℝ) ≤ P.D by exact_mod_cast hr.trans hp.le) hδ)
  simpa only [sub_add_cancel] using hh p le_rfl

theorem coherent_profile_high_bound (P : WTParams) (hd : 1 ≤ P.d)
    (hδ : 0 ≤ P.δ) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal C)
    {p : ℕ} (hp : p < P.D) :
    SNormR (40 * P.d + 1 + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1))
      (P.φ (P.δ * p)) ≤ ENNReal.ofReal C := by
  have hb := coherent_modification_orders P hd hp
  have hΛ := Lambda_antitone P hd (Nat.zero_le p)
  have ht : P.δ * p ∈ Icc (0 : ℝ) P.τstar := by
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg p), ?_⟩
    rw [htime]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show (p : ℝ) ≤ P.D by exact_mod_cast hp.le) hδ
  exact SNorm_mono_bound (hb.1.trans hΛ) (hb.2.trans hΛ) _
    (Complex.ofRealCLM.contDiff.comp ((P.φ (P.δ * p)).smooth _)) C hC (hφ _ ht)

theorem coherent_input_high_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    {C : ℝ} (hC : 0 ≤ C)
    (hφ : SNormR (40 * P.d + 1 + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1))
      (P.φ (P.δ * p)) ≤ ENNReal.ofReal C) :
    SNormR (40 * P.d + 1 + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1))
      (inputsF P R p) ≤ ENNReal.ofReal (C + 1) := by
  have hr := coherent_remainder_high_bound P hd hL hp R hR
  have hrone := hr.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr (theta_nonneg P p))))
  have hcφ := Complex.ofRealCLM.contDiff.comp ((P.φ (P.δ * p)).smooth
    (40 * P.d + 1 + 4 * P.Lambda (p + 1)))
  have hcR := contDiff_of_SNorm_bound (by omega : 40 * P.d + 1 + 4 * P.Lambda (p + 1) ≠ 0)
    (fun k => (R p k : ℂ)) 1 hrone
  have hh := SNorm_add_bound _ _ hcφ hcR C 1 hC zero_le_one hφ hrone
  have he : ((Complex.ofRealCLM ∘ (P.φ (P.δ * p))) + fun k => (R p k : ℂ)) =
      (fun k => (inputsF P R p k : ℂ)) := by
    funext k
    simp only [inputsF, Complex.ofReal_add, Pi.add_apply, Function.comp_def, Complex.ofRealCLM_apply]
  rw [he] at hh
  exact hh

end WaveTurbulence.LGSpine

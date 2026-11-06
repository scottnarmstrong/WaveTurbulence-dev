/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentProfileInputBounds
/-! The same fixed high profile constant controls every earlier layer needed by incoherent kernels. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem all_stage_input_bounds (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hδ : 0 ≤ P.δ) (htime : P.τstar = (P.D : ℝ) * P.δ)
    (hlow : LowProfileAt P) (hC₁ : 1 ≤ P.C₁)
    {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal C)
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) :
    ∀ r ≤ p,
      ContDiff ℝ (40 * P.d + 4 * P.Lambda (p + 1) : ℕ) (inputsF P R r) ∧
      SNormR (40 * P.d + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1))
        (inputsF P R r) ≤ ENNReal.ofReal (C + 1) ∧
      SNormR (40 * P.d) (40 * P.d) (inputsF P R r) ≤ ENNReal.ofReal P.C₁ := by
  have horders := (coherent_modification_orders P hd hp).2
  have hΛ := Lambda_antitone P hd (Nat.zero_le p)
  have htime_r : ∀ r ≤ p, P.δ * r ∈ Icc (0 : ℝ) P.τstar := by
    intro r hr
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg r), ?_⟩
    rw [htime]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show (r : ℝ) ≤ P.D by exact_mod_cast hr.trans hp.le) hδ
  have hh := inputsF_SNormR_bound P hd hL hp horders horders R hR C hC (by
    intro r hr
    exact SNorm_mono_bound (horders.trans hΛ) (horders.trans hΛ) _
      (Complex.ofRealCLM.contDiff.comp ((P.φ (P.δ * r)).smooth _)) C hC (hφ _ (htime_r r hr)))
  have h40 := forty_dim_le_Lambda P hd hp.le
  have hhlow := inputsF_SNormR_bound P hd hL hp h40 h40 R hR (P.C₁ - 1) (by linarith)
    (fun r hr => hlow _ (htime_r r hr))
  intro r hr
  refine ⟨contDiff_real_of_SNormR_bound (by omega : 40 * P.d + 4 * P.Lambda (p + 1) ≠ 0)
    _ _ (hh r hr), hh r hr, ?_⟩
  simpa only [sub_add_cancel] using hhlow r hr

end WaveTurbulence.LGSpine

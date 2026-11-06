/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ModificationOrderBudget
public import WaveTurbulence.Foundations.Spine.RealSpatialInputBounds
/-! The exact source remainder premise supplies every original coherent high-norm input bound. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem coherent_modification_orders (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    40 * P.d + 1 + 4 * P.Lambda (p + 1) ≤ P.Lambda p ∧
      40 * P.d + 4 * P.Lambda (p + 1) ≤ P.Lambda p := by
  have hb := modification_order_budget P hd hp
  have hΛ := forty_dim_le_Lambda P hd (show p + 1 ≤ P.D by omega)
  constructor <;> omega

theorem coherent_remainder_high_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) :
    SNormR (40 * P.d + 1 + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1)) (R p) ≤
      ENNReal.ofReal (P.L ^ (-P.theta p)) := by
  have hb := coherent_modification_orders P hd hp
  have hΛ := forty_dim_le_Lambda P hd hp.le
  have hr := hR p le_rfl
  exact SNorm_mono_bound hb.1 hb.2 _ (contDiff_of_SNorm_bound (by omega) _ _ hr)
    _ (by positivity) hr

end WaveTurbulence.LGSpine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpatialInputBounds
/-! The source high-order input norms cover every modification needed in the spatial transfer. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem Lambda_eq_dim_mul_next (P : WTParams) {p : ℕ} (hp : p < P.D) :
    P.Lambda p = (40 * P.d) * P.Lambda (p + 1) := by
  have he : P.D + 1 - p = (P.D + 1 - (p + 1)) + 1 := by omega
  unfold WTParams.Lambda
  rw [he, pow_succ, Nat.mul_comm]

theorem modification_order_budget (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    40 * P.d + 8 * P.Lambda (p + 1) ≤ P.Lambda p := by
  have hΛ := forty_dim_le_Lambda P hd (show p + 1 ≤ P.D by omega)
  rw [Lambda_eq_dim_mul_next P hp]
  calc
    _ ≤ 9 * P.Lambda (p + 1) := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega : 9 ≤ 40 * P.d)

theorem weighted_derivative_input_orders (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ}
    (hp : p < P.D) {a b : ℕ} (ha : a ≤ 4 * P.Lambda (p + 1))
    (hb : b ≤ 8 * P.Lambda (p + 1)) :
    40 * P.d + a ≤ P.Lambda p ∧ 40 * P.d + b ≤ P.Lambda p := by
  have hh := modification_order_budget P hd hp
  constructor <;> omega

end WaveTurbulence.LGSpine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductParameters
public import WaveTurbulence.Foundations.XChain.JbrBounds
/-! The fixedpoint spatial remainder estimate implies the exact final ansatz root weight. -/
public section
namespace WaveTurbulence.Induct

theorem fixedpoint_remainder_final_weight {d : ℕ} {z : ℂ} (k : Mom d) (Λ N : ℝ)
    (hΛ : 0 ≤ Λ)
    (hz : ‖z‖ ≤ jbr k ^ (-(5 / 4 * Λ)) * Real.exp (-(10 * N))) :
    ‖z‖ ≤ Real.exp (-(10 * N)) * jbr k ^ (-Λ) := by
  have hw : jbr k ^ (-(5 / 4 * Λ)) ≤ jbr k ^ (-Λ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_jbr k) (by linarith)
  exact hz.trans ((mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le).trans_eq (mul_comm _ _))

end WaveTurbulence.Induct

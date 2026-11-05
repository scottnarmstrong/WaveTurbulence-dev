/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
/-! Elementary parameter inequalities used by the inductive gluing step. -/
public section
namespace WaveTurbulence.Induct

theorem lambda_succ_ge (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    40 * P.d ≤ P.Lambda (p + 1) := by
  have he : 1 ≤ P.D + 1 - (p + 1) := by omega
  have hb : 0 < 40 * P.d := by omega
  simpa only [WTParams.Lambda, pow_one] using Nat.pow_le_pow_right hb he

theorem fixedpoint_weight_ge (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    (P.d : ℝ) + 1 ≤ 5 / 4 * P.Lambda (p + 1) := by
  have h := lambda_succ_ge P hd hp
  have hr : (40 : ℝ) * P.d ≤ P.Lambda (p + 1) := by exact_mod_cast h
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  linarith

theorem fixedpoint_weight_le_tree_weight (P : WTParams) (p : ℕ) :
    5 / 4 * (P.Lambda (p + 1) : ℝ) ≤ 3 / 2 * P.Lambda (p + 1) := by
  have h : (0 : ℝ) ≤ P.Lambda (p + 1) := Nat.cast_nonneg _
  linarith

end WaveTurbulence.Induct

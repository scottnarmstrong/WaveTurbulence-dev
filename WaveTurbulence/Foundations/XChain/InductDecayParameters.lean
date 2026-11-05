/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! The induction exponents leave sufficient root decay and lattice summability after splitting. -/
public section
namespace WaveTurbulence.Induct

theorem lambda_eq_base_mul_succ (P : WTParams) {p : ℕ} (hp : p < P.D) :
    P.Lambda p = (40 * P.d) * P.Lambda (p + 1) := by
  have he : P.D + 1 - p = (P.D + 1 - (p + 1)) + 1 := by omega
  unfold WTParams.Lambda
  rw [he, pow_succ, mul_comm]

theorem lambda_quarter_ge_dimension (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 4 := by
  have he : (P.Lambda p : ℝ) = 40 * P.d * P.Lambda (p + 1) := by
    exact_mod_cast lambda_eq_base_mul_succ P hp
  have hs : (40 : ℝ) * P.d ≤ P.Lambda (p + 1) := by
    exact_mod_cast lambda_succ_ge P hd hp
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  nlinarith

theorem lambda_quarter_ge_succ (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    (P.Lambda (p + 1) : ℝ) ≤ (P.Lambda p : ℝ) / 4 := by
  have he : (P.Lambda p : ℝ) = 40 * P.d * P.Lambda (p + 1) := by
    exact_mod_cast lambda_eq_base_mul_succ P hp
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hs : (0 : ℝ) ≤ P.Lambda (p + 1) := Nat.cast_nonneg _
  nlinarith

theorem lambda_quarter_ge_twice_succ (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    2 * (P.Lambda (p + 1) : ℝ) ≤ (P.Lambda p : ℝ) / 4 := by
  have he : (P.Lambda p : ℝ) = 40 * P.d * P.Lambda (p + 1) := by
    exact_mod_cast lambda_eq_base_mul_succ P hp
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hs : (0 : ℝ) ≤ P.Lambda (p + 1) := Nat.cast_nonneg _
  nlinarith

end WaveTurbulence.Induct

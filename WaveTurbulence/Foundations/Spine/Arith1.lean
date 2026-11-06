/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-! Per-ladder real inequalities of TARGET L2038 (`(log L)^z D^z δ^{1+10ν} / (z-d)! ≤ L^{δ^{8ν}}`). -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder

theorem Dl_sq {δ ν : ℝ} (hδ : 0 < δ) : (δ ^ (-1 / 2 - 5 * ν)) ^ 2 = δ ^ (-1 - 10 * ν) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; push_cast; ring

theorem one_le_Dl {δ ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) : 1 ≤ δ ^ (-1 / 2 - 5 * ν) := by
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
  linarith

/-- `x^K / K! ≤ Dl^{2K} exp(x δ^{1+10ν})`. -/
theorem pow_div_fact_le {δ ν x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (K : ℕ) :
    x ^ K / (Nat.factorial K : ℝ) ≤
      ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ K * Real.exp (x * δ ^ (1 + 10 * ν)) := by
  have hD : 0 < (δ ^ (-1 / 2 - 5 * ν)) ^ 2 := by positivity
  have h1 : (δ ^ (-1 / 2 - 5 * ν)) ^ 2 * δ ^ (1 + 10 * ν) = 1 := by
    rw [Dl_sq hδ, ← Real.rpow_add hδ]; norm_num
  have h2 := Real.pow_div_factorial_le_exp (x * δ ^ (1 + 10 * ν)) (by positivity) K
  have h3 : x ^ K / (Nat.factorial K : ℝ) = ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ K *
      ((x * δ ^ (1 + 10 * ν)) ^ K / (Nat.factorial K : ℝ)) := by
    have h4 : ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ K * (δ ^ (1 + 10 * ν)) ^ K = 1 := by
      rw [← mul_pow, h1, one_pow]
    have e : ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ K * (x ^ K * (δ ^ (1 + 10 * ν)) ^ K / (Nat.factorial K : ℝ)) =
        (((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ K * (δ ^ (1 + 10 * ν)) ^ K) * x ^ K / (Nat.factorial K : ℝ) := by ring
    rw [mul_pow, e, h4, one_mul]
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem small_factor {δ ν Dt ρ X Y Λ a dR Lam C1 c1 c2 c3 e f : ℝ} {m K d : ℕ}
    (hX : 1 ≤ X) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hDt : 0 ≤ Dt)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ f * a * X) (hY1 : 1 ≤ Y) (hY : Y ≤ c2 * dR * Λ) (ha : 1 ≤ a)
    (hd : (d : ℝ) = dR) (hdR : 1 ≤ dR) (hmK : m ≤ K + d + 1) (hKm : K ≤ m)
    (hc1 : 0 < c1) (hc2 : 1 ≤ c2) (hc3 : 1 ≤ c3) (hef : e * f = c3) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4) ≤ Lam)
    (hC : c1 * (c2 * dR) * (c3 * a) ≤ C1) :
    c1 ^ (2 * m + 2) * ((e * ρ * Dt) ^ K / (Nat.factorial K : ℝ)) * Y ^ (2 * m + 2 - K) ≤
      (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ (2 * m + 2) * Lam * X ^ m := by
  set Dl := δ ^ (-1 / 2 - 5 * ν) with hDl
  have hDl1 : 1 ≤ Dl := one_le_Dl hδ hδ1 hν
  have hDlpos : 0 < Dl := by linarith
  have hKm1 : K ≤ m + 1 := by omega
  have hΛ0 : 0 < Λ := by linarith
  have hc2' : 1 ≤ c2 * dR := by nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hLam : 0 ≤ Lam := le_trans (by positivity) hexp
  have hC1 : 0 ≤ C1 := le_trans (by positivity) hC
  have e1 : (e * ρ * Dt) ^ K ≤ ((c3 * a * Dt) ^ K) * X ^ m := by
    calc (e * ρ * Dt) ^ K ≤ (e * (f * a * X) * Dt) ^ K := by gcongr
      _ = (c3 * a * Dt) ^ K * X ^ K := by rw [← mul_pow, ← hef]; ring
      _ ≤ (c3 * a * Dt) ^ K * X ^ m := by
          gcongr
  have e2 : Y ^ (2 * m + 2 - K) ≤ (c2 * dR) ^ (2 * m + 2) * (Λ ^ K * Λ ^ (2 * d + 4)) := by
    calc Y ^ (2 * m + 2 - K) ≤ (c2 * dR * Λ) ^ (2 * m + 2 - K) := by gcongr
      _ = (c2 * dR) ^ (2 * m + 2 - K) * Λ ^ (2 * m + 2 - K) := mul_pow _ _ _
      _ ≤ (c2 * dR) ^ (2 * m + 2) * (Λ ^ K * Λ ^ (2 * d + 4)) := by
          apply mul_le_mul
          · apply pow_le_pow_right₀ hc2' (by omega)
          · rw [← pow_add]; apply pow_le_pow_right₀ hΛ (by omega)
          · positivity
          · positivity
  have e3 := pow_div_fact_le (δ := δ) (ν := ν) (x := Dt * Λ) hδ (by positivity) K
  have e4 : ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ K ≤ Dl ^ (2 * m + 2) := by
    rw [← hDl, ← pow_mul]; apply pow_le_pow_right₀ hDl1; omega
  have hK0 : (0 : ℝ) < (Nat.factorial K : ℝ) := by positivity
  have hmain : (c3 * a * Dt) ^ K * Λ ^ K / (Nat.factorial K : ℝ) ≤ (c3 * a) ^ (2 * m + 2) *
      (Dl ^ (2 * m + 2) * Real.exp (Dt * Λ * δ ^ (1 + 10 * ν))) := by
    have : (c3 * a * Dt) ^ K * Λ ^ K / (Nat.factorial K : ℝ) = (c3 * a) ^ K * ((Dt * Λ) ^ K / (Nat.factorial K : ℝ)) := by
      rw [mul_pow, mul_pow, mul_pow]; ring
    rw [this]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · exact pow_le_pow_right₀ (by nlinarith) (by omega)
    · exact e3.trans (mul_le_mul e4 le_rfl (by positivity) (by positivity))
  calc c1 ^ (2 * m + 2) * ((e * ρ * Dt) ^ K / (Nat.factorial K : ℝ)) * Y ^ (2 * m + 2 - K)
      ≤ c1 ^ (2 * m + 2) * ((((c3 * a * Dt) ^ K) * X ^ m) / (Nat.factorial K : ℝ)) *
          ((c2 * dR) ^ (2 * m + 2) * (Λ ^ K * Λ ^ (2 * d + 4))) := by
        gcongr
    _ = (c1 * (c2 * dR)) ^ (2 * m + 2) * X ^ m * Λ ^ (2 * d + 4) *
          ((c3 * a * Dt) ^ K * Λ ^ K / (Nat.factorial K : ℝ)) := by
        rw [mul_pow c1]; ring
    _ ≤ (c1 * (c2 * dR)) ^ (2 * m + 2) * X ^ m * Λ ^ (2 * d + 4) *
          ((c3 * a) ^ (2 * m + 2) * (Dl ^ (2 * m + 2) * Real.exp (Dt * Λ * δ ^ (1 + 10 * ν)))) := by
        gcongr
    _ = (c1 * (c2 * dR)) ^ (2 * m + 2) * (c3 * a) ^ (2 * m + 2) * Dl ^ (2 * m + 2) * X ^ m *
          (Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4)) := by
        ring
    _ = (c1 * (c2 * dR) * (c3 * a)) ^ (2 * m + 2) * Dl ^ (2 * m + 2) * X ^ m *
          (Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4)) := by
        rw [mul_pow (c1 * (c2 * dR))]
    _ ≤ (C1 * Dl) ^ (2 * m + 2) * X ^ m * Lam := by
        rw [mul_pow C1]
        have h1 : (c1 * (c2 * dR) * (c3 * a)) ^ (2 * m + 2) ≤ C1 ^ (2 * m + 2) :=
          pow_le_pow_left₀ (by positivity) hC _
        calc (c1 * (c2 * dR) * (c3 * a)) ^ (2 * m + 2) * Dl ^ (2 * m + 2) * X ^ m *
              (Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4))
            ≤ C1 ^ (2 * m + 2) * Dl ^ (2 * m + 2) * X ^ m * Lam := by gcongr
          _ = _ := by ring
    _ = _ := by ring

theorem large_factor {δ ν Y Λ dR Lam C1 c1 c2 : ℝ} {m : ℕ}
    (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hY1 : 1 ≤ Y) (hY : Y ≤ c2 * dR * Λ)
    (hdR : 1 ≤ dR) (hc1 : 0 < c1) (hc2 : 1 ≤ c2) (hΛLam : Λ ^ 2 ≤ Lam)
    (hC : c1 * (c2 * dR) ≤ C1) :
    c1 ^ (2 * m + 2) * Y ^ (2 * m + 2) ≤ (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ (2 * m + 2) * Lam * (Λ ^ 2) ^ m := by
  have hDl1 : 1 ≤ δ ^ (-1 / 2 - 5 * ν) := one_le_Dl hδ hδ1 hν
  have hC1 : 0 ≤ C1 := le_trans (by nlinarith) hC
  have h1 : c1 ^ (2 * m + 2) * Y ^ (2 * m + 2) ≤ (c1 * (c2 * dR)) ^ (2 * m + 2) * Λ ^ (2 * m + 2) := by
    rw [← mul_pow]
    calc (c1 * Y) ^ (2 * m + 2) ≤ (c1 * (c2 * dR * Λ)) ^ (2 * m + 2) := by gcongr
      _ = _ := by rw [← mul_pow]; ring_nf
  have h2 : (c1 * (c2 * dR)) ^ (2 * m + 2) ≤ (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ (2 * m + 2) := by
    apply pow_le_pow_left₀ (by positivity)
    calc c1 * (c2 * dR) ≤ C1 := hC
      _ = C1 * 1 := by ring
      _ ≤ _ := by gcongr
  have h3 : Λ ^ (2 * m + 2) ≤ Lam * (Λ ^ 2) ^ m := by
    calc Λ ^ (2 * m + 2) = Λ ^ 2 * (Λ ^ 2) ^ m := by rw [← pow_mul]; ring
      _ ≤ Lam * (Λ ^ 2) ^ m := by gcongr
  calc _ ≤ (c1 * (c2 * dR)) ^ (2 * m + 2) * Λ ^ (2 * m + 2) := h1
    _ ≤ (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ (2 * m + 2) * (Lam * (Λ ^ 2) ^ m) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.Ladder

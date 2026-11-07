/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepGate3
public import WaveTurbulence.Foundations.Stage1.Represents.RepTriv3
public import WaveTurbulence.Foundations.Stage1.Represents.RepConj3
import Mathlib.Tactic

/-!
# S2 REPRESENTS: per-slot mass bounds in the target normalisation

Gate constant `c₁ = Pg.C₁`; target constant `C` (the `C₁` of the piece); `x = C √δ`; per-slot bound
`K x^{size} L^{-η^8 g} · cost` with `K` independent of `C` as soon as `C ≥ 2 c₁² (1 + c_Leib)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic Set
open scoped ENNReal

/-- The real value of `regBound`. -/
theorem regBound_eq (P : WTParams) (n g : ℕ) :
    regBound P n g = ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) := rfl

theorem regBound_le_target (P : WTParams) (C : ℝ) (n g : ℕ) (hn : 1 ≤ n) (hc : 1 ≤ P.C₁) (hCc : P.C₁ ≤ C)
    (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hκ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) :
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) ≤
      (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
  have hC1 : 1 ≤ C := le_trans hc hCc
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL
  have h1 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) ≤ P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    nlinarith
  have h2 : (C * Real.sqrt P.δ) ^ (2 * n) = C ^ (2 * n) * P.δ ^ n := by
    rw [mul_pow, pow_mul C 2 n, pow_mul (Real.sqrt P.δ) 2 n, Real.sq_sqrt hδ]
  rw [h2]
  have h3 : P.C₁ * (P.C₁ * P.δ) ^ n ≤ C ^ (2 * n) * P.δ ^ n := by
    rw [mul_pow, ← mul_assoc, ← pow_succ']
    have : P.C₁ ^ (n + 1) ≤ C ^ (2 * n) := by
      calc P.C₁ ^ (n + 1) ≤ C ^ (n + 1) := pow_le_pow_left₀ (by linarith) hCc _
        _ ≤ C ^ (2 * n) := pow_le_pow_right₀ hC1 (by omega)
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hδ _)
  have h4 : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg hL0.le _
  calc _ ≤ (C ^ (2 * n) * P.δ ^ n) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) :=
        mul_le_mul_of_nonneg_right h3 h4
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem enn_mul_ofReal {C : ℝ≥0∞} (hC : C ≠ ⊤) (a : ℝ) (ha : 0 ≤ a) :
    C * ENNReal.ofReal a = ENNReal.ofReal (C.toReal * a) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]

/-- Bundled standing hypotheses on the gate parameter record. -/
structure GateEnv (P : WTParams) : Prop where
  hd1 : 1 ≤ P.d
  hL1 : 1 ≤ P.L
  hη0 : 0 ≤ P.η
  hη : P.η ≤ 1 / 2
  hC1 : 1 ≤ P.C₁
  hδ0 : 0 ≤ P.δ
  hκ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η
  hinc : LeafwiseIncoherentDecayAt P
  hcoh : LeafwiseCoherentApproximationAt P

theorem sep_le_target (c₁ δ cL C cost : ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : 1 ≤ c₁) (hδ : 0 ≤ δ) (hcL : 0 ≤ cL)
    (hcost : 0 ≤ cost) (hC : 2 * c₁ ^ 2 * (1 + cL) ≤ C) :
    2 ^ n * (cL * (δ ^ n * (c₁ * c₁ ^ n * cost)) * (c₁ * c₁ ^ n)) ≤
      (C * Real.sqrt δ) ^ (2 * n) * cost := by
  have h2 : (C * Real.sqrt δ) ^ (2 * n) = C ^ (2 * n) * δ ^ n := by
    rw [mul_pow, pow_mul C 2 n, pow_mul (Real.sqrt δ) 2 n, Real.sq_sqrt hδ]
  rw [h2]
  have hc2 : 1 ≤ c₁ ^ 2 := one_le_pow₀ hc
  have hC1 : 1 ≤ C := by nlinarith
  have h3 : cL * c₁ ^ 2 ≤ C := by nlinarith
  have h4 : 2 * c₁ ^ 2 ≤ C := by nlinarith
  have h5 : (2 * c₁ ^ 2) ^ n ≤ C ^ n := pow_le_pow_left₀ (by positivity) h4 _
  have h6 : cL * c₁ ^ 2 * (2 * c₁ ^ 2) ^ n ≤ C ^ (2 * n) := by
    calc cL * c₁ ^ 2 * (2 * c₁ ^ 2) ^ n ≤ C * C ^ n := mul_le_mul h3 h5 (by positivity) (by linarith)
      _ = C ^ (n + 1) := by rw [pow_succ']
      _ ≤ C ^ (2 * n) := pow_le_pow_right₀ hC1 (by omega)
  have e : 2 ^ n * (cL * (δ ^ n * (c₁ * c₁ ^ n * cost)) * (c₁ * c₁ ^ n)) =
      (cL * c₁ ^ 2 * (2 * c₁ ^ 2) ^ n) * (δ ^ n * cost) := by
    have h : (c₁ ^ 2) ^ n = c₁ ^ n * c₁ ^ n := by rw [← pow_mul, two_mul, pow_add]
    rw [mul_pow, h]
    ring
  rw [e]
  calc _ ≤ C ^ (2 * n) * (δ ^ n * cost) := mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = _ := by ring

end WaveTurbulence.Represents

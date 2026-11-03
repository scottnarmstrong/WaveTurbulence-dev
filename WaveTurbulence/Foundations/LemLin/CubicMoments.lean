/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicMomentStep

/-!
# Arbitrary coordinate frequency moments

Repeated integration by parts preserves the stationary gain and costs one
power of `1+|s|+|t|` per frequency moment. Constants depend only on the order
and the three fixed scalar amplitudes.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- Every fixed coordinate frequency moment retains stationary decay. -/
theorem scalarCubic_moments (N : ℕ) (f : Fin 3 → ScalarCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kind : CubicPhase) (s t : ℝ) (ν : Fin 3 → ℝ) (j : Fin 3),
      cubicScale s t * |ν j| ^ N * ‖scalarCubicIntegral kind f s t ν‖ ≤
        C * cubicScale s t ^ N := by
  induction N generalizing f with
  | zero =>
    refine ⟨scalarStationaryConstant f, scalarStationaryConstant_nonneg f, ?_⟩
    intro kind s t ν j
    simpa only [pow_zero, mul_one] using scalarCubic_stationary kind f s t ν
  | succ N ih =>
    choose D hD0 hD using fun j : Fin 3 => ih (Function.update f j (f j).differentiate)
    choose M hM0 hM using fun k : Fin 3 => ih (Function.update f k (f k).mulCoordinate)
    refine ⟨(∑ j, D j) + (4 * Real.pi) * ∑ k, M k,
      add_nonneg (sum_nonneg (fun j _ => hD0 j))
        (mul_nonneg (by positivity) (sum_nonneg (fun k _ => hM0 k))), ?_⟩
    intro kind s t ν j
    let Γ : ℝ := cubicScale s t
    let x : ℝ := |ν j|
    let u : ℝ := ‖scalarCubicIntegral kind (Function.update f j (f j).differentiate) s t ν‖
    let v (k : Fin 3) : ℝ := ‖scalarCubicIntegral kind (Function.update f k (f k).mulCoordinate) s t ν‖
    have hΓ : 1 ≤ Γ := one_le_cubicScale s t
    have hΓ0 : 0 ≤ Γ := (zero_le_one.trans hΓ)
    have hx : 0 ≤ x := abs_nonneg _
    have hrec : x * ‖scalarCubicIntegral kind f s t ν‖ ≤ u + (4 * Real.pi * Γ) * ∑ k, v k :=
      scalarCubic_frequency_le kind f s t j ν
    have hDb : Γ * x ^ N * u ≤ D j * Γ ^ N := hD j kind s t ν j
    have hMb : (Γ * x ^ N) * (∑ k, v k) ≤ (∑ k, M k) * Γ ^ N := by
      rw [mul_sum, sum_mul]
      exact sum_le_sum (fun k _ => hM k kind s t ν j)
    have hDsum : D j ≤ ∑ k, D k := single_le_sum (fun k _ => hD0 k) (mem_univ j)
    have hpow : Γ ^ N ≤ Γ ^ (N + 1) := pow_le_pow_right₀ hΓ (Nat.le_succ N)
    have hDgrowth : D j * Γ ^ N ≤ (∑ k, D k) * Γ ^ (N + 1) :=
      mul_le_mul hDsum hpow (pow_nonneg hΓ0 _) (sum_nonneg (fun k _ => hD0 k))
    calc
      _ = (Γ * x ^ N) * (x * ‖scalarCubicIntegral kind f s t ν‖) := by
        change Γ * x ^ (N + 1) * _ = _
        rw [pow_succ]
        ring
      _ ≤ (Γ * x ^ N) * (u + (4 * Real.pi * Γ) * ∑ k, v k) :=
        mul_le_mul_of_nonneg_left hrec (mul_nonneg hΓ0 (pow_nonneg hx _))
      _ = Γ * x ^ N * u + (4 * Real.pi * Γ) * ((Γ * x ^ N) * ∑ k, v k) := by ring
      _ ≤ D j * Γ ^ N + (4 * Real.pi * Γ) * ((∑ k, M k) * Γ ^ N) :=
        add_le_add hDb (mul_le_mul_of_nonneg_left hMb (by positivity))
      _ ≤ (∑ k, D k) * Γ ^ (N + 1) + (4 * Real.pi * Γ) * ((∑ k, M k) * Γ ^ N) :=
        add_le_add hDgrowth le_rfl
      _ = _ := by
        change _ = ((∑ k, D k) + (4 * Real.pi) * ∑ k, M k) * Γ ^ (N + 1)
        rw [pow_succ]
        ring

end WaveTurbulence.LemLin

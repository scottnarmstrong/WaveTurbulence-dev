/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.MainGlue.DiscreteParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# G10(c): absorption with the correct exponent gap

SEAL-PLAN §B.4 G10(c). The size threshold necessarily depends on the
positive gap between the induction exponent and the final exponent. For
`θ_p=η^20(1+2^(-p))`, the uniform gap for `p≤D` is `η^20 2^(-D)`.
This dependence is allowed by the frozen theorem's constant hierarchy.
-/

public section

namespace WaveTurbulence.MainGlue
open Filter
open scoped Topology

/-- The logarithmic power in the final probability bound eventually exceeds four. -/
theorem eventually_log_pow_ge_four {d : ℕ} (hd : 1 ≤ d) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L ≥ L₁, 4 ≤ Real.log L ^ (40 * d) := by
  have h : ∀ᶠ L : ℝ in atTop, 4 ≤ Real.log L ^ (40 * d) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 4] with L hL
    exact hL.trans (by simpa only [pow_one] using
      pow_le_pow_right₀ (by linarith only [hL] : 1 ≤ Real.log L) (show 1 ≤ 40 * d by omega))
  obtain ⟨B, hB⟩ := eventually_atTop.mp h
  exact ⟨max 1 B, le_max_left _ _, fun L hL => hB L ((le_max_right _ _).trans hL)⟩

/-- A logarithmic probability exponent dominates every prescribed linear logarithmic rate. -/
theorem log_power_ge_linear {p : ℕ} (hp : 2 ≤ p) {x B : ℝ}
    (hx1 : 1 ≤ x) (hxB : B ≤ x) : B * x ≤ x ^ p := by
  calc
    _ ≤ x * x := mul_le_mul_of_nonneg_right hxB (zero_le_one.trans hx1)
    _ = x ^ 2 := (pow_two x).symm
    _ ≤ _ := pow_le_pow_right₀ hx1 hp

/-- Once the logarithm is large, the probability tail beats the required polynomial. -/
theorem probability_tail_le_power {d : ℕ} (hd : 1 ≤ d) {θ L N : ℝ}
    (hL : 1 ≤ L) (hlog : max 1 (2 * ((d : ℝ) + θ + 1)) ≤ Real.log L)
    (hN : Real.log L ^ (40 * d) ≤ N) :
    L ^ d * Real.exp (-N / 2) ≤ L ^ (-θ) * L ^ (-(1 : ℝ)) := by
  have hLpos : 0 < L := by linarith only [hL]
  have hn := (log_power_ge_linear (show 2 ≤ 40 * d by omega)
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog)).trans hN
  have he : Real.exp (-N / 2) ≤ L ^ (-((d : ℝ) + θ + 1)) := by
    rw [Real.rpow_def_of_pos hLpos]
    apply Real.exp_le_exp.mpr
    nlinarith only [hn]
  calc
    _ ≤ L ^ d * L ^ (-((d : ℝ) + θ + 1)) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hLpos.le _)
    _ = _ := by
      rw [← Real.rpow_natCast L d, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      congr 1
      ring

/-- G10(c): one threshold works for every induction exponent above a fixed positive gap. -/
theorem eventually_absorb {d : ℕ} (hd : 1 ≤ d) {θ ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L ≥ L₁, ∀ β N : ℝ,
      θ + ε ≤ β → Real.log L ^ (40 * d) ≤ N →
      2 * L ^ (-β) + 2 * Real.sqrt 2 * C * L ^ d * Real.exp (-N / 2) ≤ L ^ (-θ) := by
  let A : ℝ := 2 * Real.sqrt 2 * C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlim : Tendsto (fun L : ℝ => 2 * L ^ (-ε) + A * L ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_rpow_neg_atTop hε).const_mul 2).add
        ((tendsto_rpow_neg_atTop one_pos).const_mul A)
  have hsmall : ∀ᶠ L : ℝ in atTop, 2 * L ^ (-ε) + A * L ^ (-(1 : ℝ)) ≤ 1 :=
    hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  have hevent : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      max 1 (2 * ((d : ℝ) + θ + 1)) ≤ Real.log L ∧
      2 * L ^ (-ε) + A * L ^ (-(1 : ℝ)) ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * ((d : ℝ) + θ + 1))), hsmall]
      with L hL hlog hsmall
    exact ⟨hL, hlog, hsmall⟩
  obtain ⟨B, hB⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro L hL β N hβ hN
  obtain ⟨hL1, hlog, hsmall⟩ := hB L ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := by linarith only [hL1]
  have hfirst : 2 * L ^ (-β) ≤ L ^ (-θ) * (2 * L ^ (-ε)) := by
    calc
      _ ≤ 2 * L ^ (-(θ + ε)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hβ])) (by norm_num)
      _ = _ := by rw [neg_add, Real.rpow_add hLpos]; ring
  have hsecond : A * L ^ d * Real.exp (-N / 2) ≤
      L ^ (-θ) * (A * L ^ (-(1 : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left (probability_tail_le_power hd hL1 hlog hN) hA
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  calc
    _ ≤ L ^ (-θ) * (2 * L ^ (-ε)) + L ^ (-θ) * (A * L ^ (-(1 : ℝ))) :=
      add_le_add hfirst hsecond
    _ = L ^ (-θ) * (2 * L ^ (-ε) + A * L ^ (-(1 : ℝ))) := by ring
    _ ≤ L ^ (-θ) * 1 := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hLpos.le _)
    _ = _ := mul_one _

end WaveTurbulence.MainGlue

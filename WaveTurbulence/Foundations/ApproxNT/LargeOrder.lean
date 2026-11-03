/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The large-order range `n ≤ (log L)^A` (packet NT6, FINDINGS F33)

All `n`-dependence of the proof beyond geometric factors `C^n` is the polynomial
`P(n) = n (8dn+1)^{8d}` (from the minor-arc factorials `(8d|F|)!` and the `n` telescoping terms).
For every fixed exponent `A`, once `L ≥ L₀(A)` we have `P(n) ≤ L^{η/2}` for all `n ≤ (log L)^A`;
the losses are then absorbed by `L^{η}`. No other use of the size of `n` is made.
-/

public section

noncomputable section

open Filter Real

namespace WaveTurbulence.ApproxNT

/-- The threshold `L₀` for the large-order range. -/
theorem exists_large_L {d : ℕ} (hd : 1 ≤ d) {γ η : ℝ} (hη0 : 0 < η)
    (hgap : 3 * η / 4 < 2 * ((d : ℝ) - 1) * (1 - γ)) (A : ℝ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 2 ≤ L ∧ 2 ≤ L ^ (η / 4) ∧
      (∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
        (n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) ≤ L ^ (η / 2)) ∧
      2 ^ (d + 1) * L ^ (η / 2) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) ≤ 1 / 2 := by
  set m : ℕ := 8 * d + 1
  set s : ℝ := η / (4 * m)
  have hm : (0 : ℝ) < m := by positivity
  have hs : 0 < s := by positivity
  have h1 : ∀ᶠ L in atTop, (2 : ℝ) ≤ L := eventually_ge_atTop 2
  have h2 : ∀ᶠ L in atTop, (2 : ℝ) ≤ L ^ (η / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  have h3 : ∀ᶠ L in atTop, ((8 * d + 1 : ℕ) : ℝ) ^ m ≤ L ^ (η / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have h4 : ∀ᶠ L in atTop, Real.log L ^ A ≤ L ^ s := by
    have h := (isLittleO_log_rpow_rpow_atTop A hs).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hL
    exact hL
  set e : ℝ := η / 2 + (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)
  have he : e < 0 := by simp only [e]; linarith
  have h5 : ∀ᶠ L : ℝ in atTop, (2 : ℝ) ^ (d + 1) * L ^ e ≤ 1 / 2 := by
    have ht := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).const_mul ((2 : ℝ) ^ (d + 1))
    rw [mul_zero] at ht
    filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with L hL
    simpa [neg_neg] using hL
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and h5))))
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨hL2, hLη, hL3, hL4, hL5⟩ := hL₀ L hL
  have hL0 : 0 < L := by linarith
  have hLs : 1 ≤ L ^ s := Real.one_le_rpow (by linarith) hs.le
  refine ⟨hL2, hLη, fun n hn => ?_, ?_⟩
  · have hns : (n : ℝ) ≤ L ^ s := hn.trans hL4
    have hb : ((8 * d * n + 1 : ℕ) : ℝ) ≤ (8 * d + 1 : ℕ) * L ^ s := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) d]
    have hnb : (n : ℝ) ≤ ((8 * d * n + 1 : ℕ) : ℝ) := by
      have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc (n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)
        ≤ ((8 * d * n + 1 : ℕ) : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) :=
          mul_le_mul_of_nonneg_right hnb (by positivity)
      _ = ((8 * d * n + 1 : ℕ) : ℝ) ^ m := by simp only [m]; ring
      _ ≤ (((8 * d + 1 : ℕ) : ℝ) * L ^ s) ^ m := pow_le_pow_left₀ (by positivity) hb m
      _ = ((8 * d + 1 : ℕ) : ℝ) ^ m * L ^ (η / 4) := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ s), ← Real.rpow_mul hL0.le]
          congr 2
          simp only [s]; field_simp
      _ ≤ L ^ (η / 4) * L ^ (η / 4) := mul_le_mul_of_nonneg_right hL3 (by positivity)
      _ = L ^ (η / 2) := by rw [← Real.rpow_add hL0]; congr 1; ring
  · calc 2 ^ (d + 1) * L ^ (η / 2) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)
        = 2 ^ (d + 1) * L ^ e := by rw [mul_assoc, ← Real.rpow_add hL0]
      _ ≤ 1 / 2 := hL5

end WaveTurbulence.ApproxNT

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.OfAny

/-!
# Second-order decay of differences of `χ_∞(x)/x`

For DH21 Lemma 5.8 (L1101–L1106) the Dirac mass in the third coefficient of
`R_{εα₁, εα₁; 0, μ₁, 0}` is removed by replacing `χ_∞(x)/x` with its average
`∫ ρ(g) χ_∞(x+g)/(x+g) dg` against a fixed compactly supported density `ρ`; the error is
integrable in `x`. We use `ρ = ½ 1_{[-1,1]}` and the bound
`|∂^k(χ_∞/x)(x) - ∂^k(χ_∞/x)(x+g)| ≤ (32 C_Φ + 8) A_χ^k (2k)! (1+|x|)^{-2}` for `|g| ≤ 1`, from
the Gevrey bound for `|x| ≤ 3` and the explicit derivatives of `1/x` for `|x| > 3`.
-/

public section

open MeasureTheory Set Filter Finset
open scoped ContDiff ENNReal Real Topology

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

theorem chiInvR_eq_inv {y : ℝ} (hy : 1 ≤ |y|) : chiInvR y = y⁻¹ := by
  rw [chiInvR, chiInfinity, chi0_eq_zero hy, sub_zero, one_div]

theorem iteratedDeriv_chiInvR_of_lt {y : ℝ} (hy : 1 < |y|) (k : ℕ) :
    iteratedDeriv k chiInvR y = (-1) ^ k * (k.factorial : ℝ) * (y ^ (k + 1))⁻¹ := by
  have hev : chiInvR =ᶠ[𝓝 y] fun z => z⁻¹ := by
    filter_upwards [(continuous_abs.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show y ∈ (fun z : ℝ => |z|) ⁻¹' Ioi 1 from hy)] with z hz
    exact chiInvR_eq_inv (le_of_lt hz)
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_eq_iterate]
  have := iter_deriv_inv (𝕜 := ℝ) k y
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast] at this
  exact this

theorem norm_iteratedDeriv_chiInvR_le (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k chiInvR x‖ ≤ CPhi * Achi ^ k * ((2 * k).factorial : ℝ) := by
  have := chiInvR_gevrey k x
  have h1 : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  calc ‖iteratedDeriv k chiInvR x‖ ≤ (1 + |x|) * ‖iteratedDeriv k chiInvR x‖ :=
        le_mul_of_one_le_left (norm_nonneg _) h1
    _ ≤ _ := by unfold CPhi; exact this

/-- `|x^{-(k+1)} - (x+g)^{-(k+1)}| ≤ 8 (1+|x|)^{-2}` for `|x| > 3`, `|g| ≤ 1`. -/
theorem abs_inv_pow_sub_le (k : ℕ) {x g : ℝ} (hx : 3 < |x|) (hg : |g| ≤ 1) :
    |(x ^ (k + 1))⁻¹ - ((x + g) ^ (k + 1))⁻¹| ≤ 8 * ((1 + |x|) ^ 2)⁻¹ := by
  set r := |x| with hr
  have hxg : r - 1 ≤ |x + g| := by
    have := abs_sub_abs_le_abs_sub x (-g)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hx0 : x ≠ 0 := fun h => by rw [h, abs_zero] at hr; linarith
  have hxg0 : x + g ≠ 0 := fun h => by rw [h, abs_zero] at hxg; linarith
  rcases k with _ | k
  · simp only [zero_add, pow_one]
    rw [inv_sub_inv hx0 hxg0, abs_div, abs_mul, show x + g - x = g by ring,
      div_le_iff₀ (by positivity)]
    have h4 : (1 + r) ^ 2 ≤ 4 * (r * (r - 1)) := by nlinarith
    have h5 : 1 / 4 ≤ ((1 + r) ^ 2)⁻¹ * (r * (r - 1)) := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
    have h6 : ((1 + r) ^ 2)⁻¹ * (r * (r - 1)) ≤ ((1 + r) ^ 2)⁻¹ * (r * |x + g|) := by
      have : 0 ≤ ((1 + r) ^ 2)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxg (by linarith)) this
    nlinarith [abs_nonneg g]
  · have hr1 : 0 < r - 1 := by linarith
    have ha : |(x ^ (k + 1 + 1))⁻¹| ≤ ((r - 1) ^ 2)⁻¹ := by
      rw [abs_inv, abs_pow]
      have : (r - 1) ^ 2 ≤ r ^ (k + 1 + 1) :=
        le_trans (pow_le_pow_left₀ hr1.le (by linarith : r - 1 ≤ r) 2)
          (pow_le_pow_right₀ (by linarith) (by omega))
      exact inv_anti₀ (by positivity) this
    have hb : |((x + g) ^ (k + 1 + 1))⁻¹| ≤ ((r - 1) ^ 2)⁻¹ := by
      rw [abs_inv, abs_pow]
      have : (r - 1) ^ 2 ≤ |x + g| ^ (k + 1 + 1) :=
        le_trans (pow_le_pow_left₀ hr1.le hxg 2) (pow_le_pow_right₀ (by linarith) (by omega))
      exact inv_anti₀ (by positivity) this
    have hc : 2 * ((r - 1) ^ 2)⁻¹ ≤ 8 * ((1 + r) ^ 2)⁻¹ := by
      have h4 : (1 + r) ^ 2 ≤ 4 * (r - 1) ^ 2 := by nlinarith
      calc 2 * ((r - 1) ^ 2)⁻¹ = 8 * (4 * (r - 1) ^ 2)⁻¹ := by rw [mul_inv]; ring
        _ ≤ 8 * ((1 + r) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h4) (by norm_num)
    calc |(x ^ (k + 1 + 1))⁻¹ - ((x + g) ^ (k + 1 + 1))⁻¹|
        ≤ |(x ^ (k + 1 + 1))⁻¹| + |((x + g) ^ (k + 1 + 1))⁻¹| := abs_sub _ _
      _ ≤ 2 * ((r - 1) ^ 2)⁻¹ := by linarith
      _ ≤ 8 * ((1 + r) ^ 2)⁻¹ := hc

/-- **The averaging error of `χ_∞(x)/x` decays like `(1+|x|)^{-2}`.** -/
theorem norm_chiInvR_diff_le (k : ℕ) (x g : ℝ) (hg : |g| ≤ 1) :
    ‖iteratedDeriv k chiInvR x - iteratedDeriv k chiInvR (x + g)‖ ≤
      (32 * CPhi + 8) * (Achi ^ k * ((2 * k).factorial : ℝ)) * ((1 + |x|) ^ 2)⁻¹ := by
  have hA1 : (1 : ℝ) ≤ Achi ^ k := one_le_pow₀ (by linarith [two_le_Achi])
  have hf : (k.factorial : ℝ) ≤ ((2 * k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hCP := CPhi_nonneg
  set G := Achi ^ k * ((2 * k).factorial : ℝ) with hG
  have hG0 : 0 ≤ G := by positivity
  have hG1 : (k.factorial : ℝ) ≤ G := hf.trans (le_mul_of_one_le_left (by positivity) hA1)
  have hinv0 : 0 ≤ ((1 + |x|) ^ 2)⁻¹ := by positivity
  by_cases hx : |x| ≤ 3
  · have hb : 1 / 16 ≤ ((1 + |x|) ^ 2)⁻¹ := by
      rw [one_div]
      refine inv_anti₀ (by positivity) ?_
      nlinarith [abs_nonneg x]
    have e : ∀ y, ‖iteratedDeriv k chiInvR y‖ ≤ CPhi * G := fun y => by
      rw [hG, ← mul_assoc]; exact norm_iteratedDeriv_chiInvR_le k y
    calc ‖iteratedDeriv k chiInvR x - iteratedDeriv k chiInvR (x + g)‖
        ≤ ‖iteratedDeriv k chiInvR x‖ + ‖iteratedDeriv k chiInvR (x + g)‖ := norm_sub_le _ _
      _ ≤ CPhi * G + CPhi * G := add_le_add (e x) (e (x + g))
      _ ≤ (32 * CPhi + 8) * G * ((1 + |x|) ^ 2)⁻¹ := by
          have := mul_le_mul_of_nonneg_left hb (mul_nonneg hCP hG0)
          nlinarith
  · rw [not_le] at hx
    have hxg : |x| - 1 ≤ |x + g| := by
      have := abs_sub_abs_le_abs_sub x (-g)
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    rw [iteratedDeriv_chiInvR_of_lt (by linarith) k,
      iteratedDeriv_chiInvR_of_lt (by linarith) k, Real.norm_eq_abs,
      show (-1) ^ k * (k.factorial : ℝ) * (x ^ (k + 1))⁻¹ -
        (-1) ^ k * (k.factorial : ℝ) * ((x + g) ^ (k + 1))⁻¹ =
        (-1) ^ k * (k.factorial : ℝ) * ((x ^ (k + 1))⁻¹ - ((x + g) ^ (k + 1))⁻¹) by ring,
      abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast]
    have h := abs_inv_pow_sub_le k hx hg
    calc (k.factorial : ℝ) * |(x ^ (k + 1))⁻¹ - ((x + g) ^ (k + 1))⁻¹|
        ≤ G * (8 * ((1 + |x|) ^ 2)⁻¹) :=
          mul_le_mul hG1 h (abs_nonneg _) hG0
      _ ≤ (32 * CPhi + 8) * G * ((1 + |x|) ^ 2)⁻¹ := by
          nlinarith [mul_nonneg (mul_nonneg hCP hG0) hinv0]

end WaveTurbulence.ClassJR

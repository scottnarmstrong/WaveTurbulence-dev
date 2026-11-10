/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.WeightDiff
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (b): Leibniz packaging of the weights

The weights of the clause (b) rows are products and shifts of the separated momentum factors
`M_Q ∈ 𝔖^{A+1,W}`, `M_T ∈ 𝔖^{A+1,0}`:

* `SNorm_mul_le` (weighted Leibniz bound; copied from `pl23-30d` `PL234Draft/SepCalc.lean`,
  sha256 `9012a6a5…`, see `COPIED-SHA256SUMS`);
* `SNorm_translate_le`: a unit shift costs `2^W`;
* `kq_IIa`, `kq_IIb`, `kt_IIa`, `kt_IIb`: the exact `K`-slot and `L`-slot weight bounds for the
  four (b) rows (couple/tree × Vine II-a/II-b), in `𝔖^{A,W}` / `𝔖^{A,0}`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset WaveTurbulence.LGSpine
open scoped ENNReal

namespace WaveTurbulence.VineEstS4c

variable {d : ℕ}

theorem SNorm_mul_le {A B : ℕ} (hd : 1 ≤ d) (f g : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (hg : ContDiff ℝ A g) {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hF : SNorm A 0 f ≤ ENNReal.ofReal Cf) (hG : SNorm A B g ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun x => f x * g x) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cf * Cg) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply SNorm_le_of_momentum_bounds _ (hf.mul hg)
  intro n hn ρ x
  apply (mul_le_mul_of_nonneg_left (norm_momentumDerivative_le_frechet' _ ρ x)
    (pow_nonneg (jbr_pos x).le B)).trans
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hn))
    (pow_nonneg (jbr_pos x).le B)).trans
  rw [mul_sum]
  have hterm (i : ℕ) (hi : i ∈ range (n + 1)) :
      jbr x ^ B * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
      (n.choose i : ℝ) * ((d : ℝ) ^ A * Cf * Cg) := by
    have hiA : i ≤ A := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
    have hni : n - i ≤ A := (Nat.sub_le _ _).trans hn
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hf0 := SNorm_frechet_pointwise f hf Cf hCf hF hiA x
    rw [pow_zero, one_mul] at hf0
    have hg0 := SNorm_frechet_pointwise g hg Cg hCg hG hni x
    have hdn : (d : ℝ) ^ i * (d : ℝ) ^ (n - i) ≤ (d : ℝ) ^ A := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hd1 (by omega)
    have hch : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc jbr x ^ B * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖)
        = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * (jbr x ^ B * ‖iteratedFDeriv ℝ (n - i) g x‖)) := by
          ring
      _ ≤ (n.choose i : ℝ) * (((d : ℝ) ^ i * Cf) * ((d : ℝ) ^ (n - i) * Cg)) := by
          apply mul_le_mul_of_nonneg_left _ hch
          exact mul_le_mul hf0 hg0 (mul_nonneg (pow_nonneg (jbr_pos x).le B) (norm_nonneg _))
            (mul_nonneg (pow_nonneg (by linarith) i) hCf)
      _ = (n.choose i : ℝ) * (((d : ℝ) ^ i * (d : ℝ) ^ (n - i)) * Cf * Cg) := by ring
      _ ≤ (n.choose i : ℝ) * ((d : ℝ) ^ A * Cf * Cg) := by
          apply mul_le_mul_of_nonneg_left _ hch
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdn hCf) hCg
  apply (sum_le_sum hterm).trans
  rw [← sum_mul]
  have hsum : (∑ i ∈ range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    simpa only [one_pow, one_mul, one_add_one_eq_two] using (add_pow (1 : ℝ) 1 n).symm
  rw [hsum]
  have hc : 0 ≤ (d : ℝ) ^ A * Cf * Cg := by positivity
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hc
  calc (2 : ℝ) ^ n * ((d : ℝ) ^ A * Cf * Cg) ≤ 2 ^ A * ((d : ℝ) ^ A * Cf * Cg) := hh
    _ = _ := by ring


/-- A unit translation costs `2^W` (Peetre). -/
theorem SNorm_translate_le {A W : ℕ} (hd : 1 ≤ d) {f : Mom d → ℂ} (hf : ContDiff ℝ A f) {β : ℝ}
    (hβ : 0 ≤ β) (h : SNorm A W f ≤ ENNReal.ofReal β) (a : Mom d) (ha : ‖a‖ ≤ 1) :
    SNorm A W (fun k => f (k + a)) ≤ ENNReal.ofReal ((2 : ℝ) ^ W * (d : ℝ) ^ A * β) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply SNorm_le_of_frechet_bounds _ (hf.comp (contDiff_id.add contDiff_const))
  intro n hn x
  show jbr x ^ W * ‖iteratedFDeriv ℝ n (fun k => f (k + a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_add_right]
  have hp := SNorm_frechet_pointwise f hf β hβ h hn (x + a)
  have hj := jbr_le_two_mul_jbr_add x a ha
  have hjx : 0 < jbr x := jbr_pos x
  calc jbr x ^ W * ‖iteratedFDeriv ℝ n f (x + a)‖
      ≤ (2 * jbr (x + a)) ^ W * ‖iteratedFDeriv ℝ n f (x + a)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hjx.le hj W) (norm_nonneg _)
    _ = 2 ^ W * (jbr (x + a) ^ W * ‖iteratedFDeriv ℝ n f (x + a)‖) := by rw [mul_pow]; ring
    _ ≤ 2 ^ W * ((d : ℝ) ^ n * β) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 2 ^ W * ((d : ℝ) ^ A * β) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hn) hβ
    _ = _ := by ring

/-- The constant weight `1` (the `L`-slot weight of a row whose `L`-factor was moved to `k`). -/
theorem SNorm_one_le (A : ℕ) : SNorm A 0 (fun _ : Mom d => (1 : ℂ)) ≤ ENNReal.ofReal 1 := by
  apply SNorm_le_of_frechet_bounds _ contDiff_const
  intro n _ x
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hn)]; simp

section Rows

variable {A W : ℕ} (hd : 1 ≤ d) {MQ MT : Mom d → ℂ} {βQ βT : ℝ} (hβQ : 0 ≤ βQ) (hβT : 0 ≤ βT)
  (hQ : SNorm (A + 1) W MQ ≤ ENNReal.ofReal βQ) (hT : SNorm (A + 1) 0 MT ≤ ENNReal.ofReal βT)

end Rows

end WaveTurbulence.VineEstS4c

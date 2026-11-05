/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# X3: Sobolev in time on a unit interval (T (sobolev), L2315)

`sq_norm_le_sobolev`: if `f(t) − f(t₀) = ∫_{t₀}^t g` for `t, t₀ ∈ [a, a+1]`, then for every `t ∈ [a, a+1]`,
`|f(t)|² ≤ 2 ∫_a^{a+1} |f|² + 2 ∫_a^{a+1} |g|²`. The first integral is parenthesized: the body of `∫ x in a..b, …`
absorbs a following `+`.

The proof:
- `|f(t)| ≤ |f(t₀)| + ∫|g|`;
- `(∫_a^{a+1} G)² ≤ ∫_a^{a+1} G²`, since `0 ≤ ∫(G − m)²` on an interval of length one;
- square, then average over `t₀`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set intervalIntegral

/-- `(∫_a^{a+1} G)² ≤ ∫_a^{a+1} G²`. -/
theorem sq_integral_le_integral_sq {a : ℝ} {G : ℝ → ℝ} (hG : IntervalIntegrable G volume a (a + 1))
    (hG2 : IntervalIntegrable (fun s => G s ^ 2) volume a (a + 1)) :
    (∫ s in a..a + 1, G s) ^ 2 ≤ ∫ s in a..a + 1, G s ^ 2 := by
  set m := ∫ s in a..a + 1, G s
  have h0 : 0 ≤ ∫ s in a..a + 1, (G s - m) ^ 2 :=
    integral_nonneg (by linarith) fun s _ => sq_nonneg _
  have hexp : ∫ s in a..a + 1, (G s - m) ^ 2 = (∫ s in a..a + 1, G s ^ 2) - m ^ 2 := by
    have e : ∀ s, (G s - m) ^ 2 = G s ^ 2 - 2 * m * G s + m ^ 2 := fun s => by ring
    simp_rw [e]
    rw [integral_add (hG2.sub (hG.const_mul _)) intervalIntegrable_const, integral_sub hG2 (hG.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul, one_mul]
    ring
  linarith

/-- **Sobolev in `t`.** -/
theorem sq_norm_le_sobolev {a : ℝ} {f g : ℝ → ℂ}
    (hfg : ∀ t ∈ Icc a (a + 1), ∀ t₀ ∈ Icc a (a + 1), f t - f t₀ = ∫ s in t₀..t, g s)
    (hg : IntervalIntegrable g volume a (a + 1))
    (hg2 : IntervalIntegrable (fun s => ‖g s‖ ^ 2) volume a (a + 1))
    (hf2 : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume a (a + 1)) {t : ℝ} (ht : t ∈ Icc a (a + 1)) :
    ‖f t‖ ^ 2 ≤ 2 * (∫ s in a..a + 1, ‖f s‖ ^ 2) + 2 * ∫ s in a..a + 1, ‖g s‖ ^ 2 := by
  set m := ∫ s in a..a + 1, ‖g s‖
  have hgn : IntervalIntegrable (fun s => ‖g s‖) volume a (a + 1) := hg.norm
  -- `|∫_{t₀}^t g| ≤ m`
  have hseg : ∀ t₀ ∈ Icc a (a + 1), ‖∫ s in t₀..t, g s‖ ≤ m := by
    intro t₀ ht₀
    have hsub : ∀ {u v : ℝ}, u ∈ Icc a (a + 1) → v ∈ Icc a (a + 1) → u ≤ v →
        ∫ s in u..v, ‖g s‖ ≤ m := fun {u v} hu hv huv =>
      integral_mono_interval hu.1 huv hv.2 (ae_of_all _ fun s => norm_nonneg _) hgn
    refine (norm_integral_le_abs_integral_norm).trans ?_
    rcases le_total t₀ t with h | h
    · rw [abs_of_nonneg (integral_nonneg h fun s _ => norm_nonneg _)]
      exact hsub ht₀ ht h
    · rw [integral_symm, abs_neg, abs_of_nonneg (integral_nonneg h fun s _ => norm_nonneg _)]
      exact hsub ht ht₀ h
  have hm2 : m ^ 2 ≤ ∫ s in a..a + 1, ‖g s‖ ^ 2 := sq_integral_le_integral_sq hgn hg2
  have hpt : ∀ t₀ ∈ Icc a (a + 1), ‖f t‖ ^ 2 ≤ 2 * ‖f t₀‖ ^ 2 + 2 * m ^ 2 := by
    intro t₀ ht₀
    have h1 : ‖f t‖ ≤ ‖f t₀‖ + m := by
      have : f t = f t₀ + (f t - f t₀) := by ring
      rw [this, hfg t ht t₀ ht₀]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (hseg t₀ ht₀))
    have hm0 : 0 ≤ m := integral_nonneg (by linarith) fun s _ => norm_nonneg _
    nlinarith [norm_nonneg (f t), norm_nonneg (f t₀), sq_nonneg (‖f t₀‖ - m)]
  -- average over `t₀`
  have hav : ‖f t‖ ^ 2 ≤ ∫ t₀ in a..a + 1, (2 * ‖f t₀‖ ^ 2 + 2 * m ^ 2) := by
    have hc : ‖f t‖ ^ 2 = ∫ _t₀ in a..a + 1, ‖f t‖ ^ 2 := by simp
    rw [hc]
    refine integral_mono_on (by linarith) intervalIntegrable_const
      ((hf2.const_mul 2).add intervalIntegrable_const) fun t₀ ht₀ => hpt t₀ ht₀
  rw [integral_add (hf2.const_mul 2) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hav
  simp only [add_sub_cancel_left, smul_eq_mul, one_mul] at hav
  refine hav.trans ?_
  gcongr

end WaveTurbulence.Fixedpt

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Basic

/-!
# Fourier decay of localized amplitudes

* `norm_integral_fourierChar_le`: for a compactly supported `C^N` function `f` on `ℝ^d`,
  `(1 + |w|)^N |∫ e(⟨x, w⟩) f(x) dx| ≤ 2·4^N ∑_{j ≤ N} ∫ |D^j f|` (integration by parts, through
  Mathlib's `Real.pow_mul_norm_iteratedFDeriv_fourier_le`);
* `norm_integral_amplitude_le`: for `f(x) = χ₀((x-a)/λ) g(x)` with `|D^k g| ≤ D` (`k ≤ N`) and
  `λ ≥ 1`, the right side is `≤ ampConst d N · D λ^d`, uniformly in `a` and `w`.

This is the only analytic input of the per-term bounds of DH23 Lemma 6.5 (non-stationary phase
in one variable, and stationary phase for `e(s⟨x,y⟩)` after integrating that variable).
-/

public section

noncomputable section

open MeasureTheory Metric
open scoped FourierTransform ContDiff

namespace WaveTurbulence.NTSP

variable {d : ℕ}

theorem one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + t ^ N) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * t ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr; linarith

/-- Fourier decay of a compactly supported `C^N` function. -/
theorem norm_integral_fourierChar_le {f : Mom d → ℂ} {N : ℕ} (hf : ContDiff ℝ N f)
    (hc : HasCompactSupport f) (w : Mom d) :
    (1 + ‖w‖) ^ N * ‖∫ x, Real.fourierChar (inner ℝ x w) • f x‖ ≤
      2 * 4 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ := by
  have hF : ‖∫ x, Real.fourierChar (inner ℝ x w) • f x‖ = ‖𝓕 f (-w)‖ := by
    simpa using Fourier.norm_oscillatory_translate_eq f 0 w
  rw [hF]
  set S := ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖
  have hint : ∀ n ≤ N, Integrable (fun x => ‖iteratedFDeriv ℝ n f x‖) := fun n hn =>
    ((hf.continuous_iteratedFDeriv (by exact_mod_cast hn)).norm).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv n).norm
  have hS0 : ∀ j ∈ Finset.range (N + 1), 0 ≤ ∫ x, ‖iteratedFDeriv ℝ j f x‖ := fun j _ =>
    integral_nonneg fun _ => norm_nonneg _
  have h0 : ‖𝓕 f (-w)‖ ≤ S := by
    refine (Real.norm_fourier_le_integral_norm f (-w)).trans ?_
    have : ∫ x, ‖f x‖ = ∫ x, ‖iteratedFDeriv ℝ 0 f x‖ := by simp [norm_iteratedFDeriv_zero]
    rw [this]
    exact Finset.single_le_sum hS0 (Finset.mem_range.2 (Nat.succ_pos N))
  have hN : ‖w‖ ^ N * ‖𝓕 f (-w)‖ ≤ 2 ^ N * S := by
    have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := N) hf
      (fun k n hk hn => by
        have hk' : k ≤ 0 := by exact_mod_cast hk
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using hint n (by exact_mod_cast hn)) (k := 0) (n := N) le_rfl le_rfl (-w)
    simp only [norm_neg, norm_iteratedFDeriv_zero, pow_zero, one_mul, zero_add,
      Finset.range_one, Finset.singleton_product, Finset.sum_map,
      Function.Embedding.sectR_apply] at h
    calc ‖w‖ ^ N * ‖𝓕 f (-w)‖ ≤ _ := h
      _ = 2 ^ N * S := by
          norm_num only [S]
          rfl
  calc (1 + ‖w‖) ^ N * ‖𝓕 f (-w)‖ ≤ 2 ^ N * (1 + ‖w‖ ^ N) * ‖𝓕 f (-w)‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le _ (norm_nonneg w) N) (norm_nonneg _)
    _ = 2 ^ N * (‖𝓕 f (-w)‖ + ‖w‖ ^ N * ‖𝓕 f (-w)‖) := by ring
    _ ≤ 2 ^ N * (S + 2 ^ N * S) := by gcongr
    _ = 2 ^ N * (1 + 2 ^ N) * S := by ring
    _ ≤ 2 * 4 ^ N * S := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg hS0)
        have h4 : (4 : ℝ) ^ N = 2 ^ N * 2 ^ N := by rw [← mul_pow]; norm_num
        have h1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
        nlinarith

/-- The constant in the amplitude decay bound. -/
@[expose] def ampConst (d N : ℕ) : ℝ :=
  2 * 4 ^ N * (N + 1) * (2 ^ N * ∑ i ∈ Finset.range (N + 1), chiDerivConst d i) *
    ((Real.sqrt d) ^ d * ballVol d)

theorem ampConst_nonneg (d N : ℕ) : 0 ≤ ampConst d N := by
  unfold ampConst
  have := ballVol_nonneg d
  have : 0 ≤ ∑ i ∈ Finset.range (N + 1), chiDerivConst d i :=
    Finset.sum_nonneg fun i _ => chiDerivConst_nonneg d i
  positivity

/-- Decay of `∫ e(⟨x, w⟩) χ₀((x-a)/λ) g(x) dx`, uniformly in `a` and `w`, for `λ ≥ 1` and
`|D^k g| ≤ D` (`k ≤ N`). -/
theorem norm_integral_amplitude_le {lam D : ℝ} (hlam : 1 ≤ lam) {N : ℕ} {g : Mom d → ℂ}
    (hg : ContDiff ℝ N g) (hgD : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ D) (a w : Mom d) :
    (1 + ‖w‖) ^ N * ‖∫ x, Real.fourierChar (inner ℝ x w) • (chiScaled lam (x - a) * g x)‖ ≤
      ampConst d N * D * lam ^ d := by
  have h0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hD : 0 ≤ D := (norm_nonneg _).trans (hgD 0 (Nat.zero_le _) 0)
  set χa : Mom d → ℂ := fun x => chiScaled lam (x - a)
  have hχ : ContDiff ℝ ∞ χa := (contDiff_chiScaled lam).comp (contDiff_id.sub contDiff_const)
  have hfc : ContDiff ℝ N (fun x => χa x * g x) := (hχ.of_le (by exact_mod_cast le_top)).mul hg
  have hsupp : ∀ x, χa x * g x ≠ 0 → x ∈ closedBall a (lam * Real.sqrt d) := fun x hx => by
    rw [mem_closedBall, dist_eq_norm]
    exact norm_le_of_chiScaled_ne_zero h0 (left_ne_zero_of_mul hx)
  have hc : HasCompactSupport (fun x => χa x * g x) := by
    refine HasCompactSupport.intro (isCompact_closedBall a (lam * Real.sqrt d)) fun x hx => ?_
    by_contra hne
    exact hx (hsupp x hne)
  set cb := ∑ i ∈ Finset.range (N + 1), chiDerivConst d i
  have hcb : 0 ≤ cb := Finset.sum_nonneg fun i _ => chiDerivConst_nonneg d i
  -- pointwise derivative bounds by Leibniz
  have hder : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (fun x => χa x * g x) x‖ ≤ 2 ^ N * cb * D :=
    fun j hj x => by
    refine (norm_iteratedFDeriv_mul_le (hχ.of_le (by exact_mod_cast le_top)) hg x
      (by exact_mod_cast hj)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χa x‖ *
          ‖iteratedFDeriv ℝ (j - i) g x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (2 ^ N : ℝ) * chiDerivConst d i * D := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have hc1 : (j.choose i : ℝ) ≤ 2 ^ N := by
            have := Nat.choose_le_two_pow j i
            calc (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast this
              _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hj
          exact mul_le_mul (mul_le_mul hc1 (norm_iteratedFDeriv_chiScaled_le hlam a i x)
            (norm_nonneg _) (by positivity)) (hgD _ (le_trans (Nat.sub_le _ _) hj) x)
            (norm_nonneg _) (mul_nonneg (by positivity) (chiDerivConst_nonneg d i))
      _ = 2 ^ N * (∑ i ∈ Finset.range (j + 1), chiDerivConst d i) * D := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ 2 ^ N * cb * D := by
          gcongr
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (Nat.succ_le_succ hj))
            (fun i _ _ => chiDerivConst_nonneg d i)
  have hint : ∀ j ∈ Finset.range (N + 1),
      ∫ x, ‖iteratedFDeriv ℝ j (fun x => χa x * g x) x‖ ≤
        2 ^ N * cb * D * ((lam * Real.sqrt d) ^ d * ballVol d) := fun j hj =>
    integral_norm_le_of_support (f := fun x => iteratedFDeriv ℝ j (fun x => χa x * g x) x)
      (by positivity) (hder j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (fun x hx => by
        by_contra hm
        apply hx
        have hx' : x ∉ tsupport (fun x => χa x * g x) := by
          intro ht
          refine hm ?_
          refine (isClosed_closedBall.closure_subset_iff.2 fun y hy => hsupp y hy) ht
        exact image_eq_zero_of_notMem_tsupport
          (fun h => hx' (tsupport_iteratedFDeriv_subset j h)))
  calc (1 + ‖w‖) ^ N * ‖∫ x, Real.fourierChar (inner ℝ x w) • (χa x * g x)‖
      ≤ 2 * 4 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j (fun x => χa x * g x) x‖ :=
        norm_integral_fourierChar_le hfc hc w
    _ ≤ 2 * 4 ^ N * ∑ _j ∈ Finset.range (N + 1),
          2 ^ N * cb * D * ((lam * Real.sqrt d) ^ d * ballVol d) := by
        gcongr with j hj
        exact hint j hj
    _ = ampConst d N * D * lam ^ d := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ampConst, mul_pow]
        push_cast
        ring

end WaveTurbulence.NTSP

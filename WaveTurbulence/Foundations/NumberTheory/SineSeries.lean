/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license; see SALT-LICENSE in this directory.
Authors: Jason Hickey, Claude
Adapted for WaveTurbulence by Scott Armstrong.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Abel bounds and the sine Fourier series of the sawtooth

NT-CIRCLE-v2 goal 1. On `(0,1)` the partial sums of `sin(2πnx)/n` tend
to `π(1/2-x)`. This is ordinary convergence, not absolute convergence.
Adapted from §§1, 3, 4 of Jason Hickey's `Salt/MR/Sawtooth.lean`, commit
`3d7274047aabeea823abf1c0bdf675ce165dbca2`, https://github.com/jyh/salt.
The unrelated Hurwitz-zeta results and their assumptions are not imported.
-/

public section

namespace WaveTurbulence.NumberTheory.SineSeries

open Complex Filter Topology Finset
open scoped Real

section AbelInequality

variable {u b : ℕ → ℝ} {B : ℝ}

/-- **Abel's inequality.**  If the partial sums of `u` are bounded by `B` and `b` is a
nonnegative antitone sequence, then `|∑_{n < M} u n * b n| ≤ B * b 0`. -/
theorem abs_sum_mul_le_of_bounded (hS : ∀ N, |∑ n ∈ range N, u n| ≤ B)
    (hb0 : ∀ n, 0 ≤ b n) (hbanti : Antitone b) (M : ℕ) :
    |∑ n ∈ range M, u n * b n| ≤ B * b 0 := by
  have hB : (0 : ℝ) ≤ B := by simpa using hS 0
  have key : ∑ n ∈ range M, u n * b n =
      b (M - 1) * (∑ i ∈ range M, u i)
        - ∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j := by
    have h := Finset.sum_range_by_parts b u M
    simp only [smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have h1 : |b (M - 1) * ∑ i ∈ range M, u i| ≤ B * b (M - 1) := by
    rw [abs_mul, abs_of_nonneg (hb0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS M) (hb0 _)
  have h2 : |∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j|
      ≤ B * (b 0 - b (M - 1)) := by
    calc |∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j|
        ≤ ∑ i ∈ range (M - 1), |(b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (M - 1), (b i - b (i + 1)) * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hbanti (Nat.le_succ i))), neg_sub]
          exact mul_le_mul_of_nonneg_left (hS _) (by linarith [hbanti (Nat.le_succ i)])
      _ = (b 0 - b (M - 1)) * B := by rw [← Finset.sum_mul, Finset.sum_range_sub' b (M - 1)]
      _ = B * (b 0 - b (M - 1)) := mul_comm _ _
  rw [key]
  calc |b (M - 1) * (∑ i ∈ range M, u i)
        - ∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j|
      ≤ |b (M - 1) * ∑ i ∈ range M, u i|
        + |∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j| := abs_sub _ _
    _ ≤ B * b (M - 1) + B * (b 0 - b (M - 1)) := add_le_add h1 h2
    _ = B * b 0 := by ring

/-- The tail form of Abel's inequality: the block of the series starting at `N` is bounded by
`2 B b N`. -/
theorem abs_sum_shift_mul_le_of_bounded (hS : ∀ N, |∑ n ∈ range N, u n| ≤ B)
    (hb0 : ∀ n, 0 ≤ b n) (hbanti : Antitone b) (N M : ℕ) :
    |∑ n ∈ range M, u (n + N) * b (n + N)| ≤ 2 * B * b N := by
  have hS' : ∀ K, |∑ n ∈ range K, u (n + N)| ≤ 2 * B := by
    intro K
    have e1 : ∑ n ∈ Finset.Ico N (N + K), u n = ∑ n ∈ range K, u (n + N) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    have e2 : ∑ n ∈ range N, u n + ∑ n ∈ Finset.Ico N (N + K), u n = ∑ n ∈ range (N + K), u n :=
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_right N K)
    have e3 : ∑ n ∈ range K, u (n + N) = (∑ n ∈ range (N + K), u n) - ∑ n ∈ range N, u n := by
      rw [← e1, ← e2]; ring
    rw [e3]
    calc |(∑ n ∈ range (N + K), u n) - ∑ n ∈ range N, u n|
        ≤ |∑ n ∈ range (N + K), u n| + |∑ n ∈ range N, u n| := abs_sub _ _
      _ ≤ B + B := add_le_add (hS _) (hS _)
      _ = 2 * B := by ring
  have h := abs_sum_mul_le_of_bounded (u := fun n => u (n + N)) (b := fun n => b (n + N)) hS'
    (fun n => hb0 _) (fun i j hij => hbanti (by omega)) M
  simpa using h

end AbelInequality

section Geometry

variable {x : ℝ}

/-- The `n`-th power of `e^{2πix}` has imaginary part `sin (2πnx)`. -/
theorem exp_pow_im (x : ℝ) (n : ℕ) :
    ((Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)) ^ n).im = Real.sin (2 * Real.pi * x * n) := by
  rw [← Complex.exp_nat_mul,
    show ((n : ℂ) * (((2 * Real.pi * x : ℝ) : ℂ) * I))
      = (((2 * Real.pi * x * n : ℝ) : ℂ)) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

/-- `sin (πx) > 0` on `(0,1)`. -/
theorem sin_pi_mul_pos (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < Real.sin (Real.pi * x) := by
  obtain ⟨hx0, hx1⟩ := hx
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  nlinarith only [hx1, Real.pi_pos]

/-- The half-angle identity `1 − cos (2πx) = 2 sin²(πx)`. -/
theorem one_sub_cos_two_pi_mul (x : ℝ) :
    1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2 := by
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul']
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

/-- **The polar form of `1 − e^{2πix}`** for `x ∈ (0,1)`: modulus `2 sin (πx) > 0`, argument
`πx − π/2 ∈ (−π/2, π/2)`. -/
theorem one_sub_exp_eq (x : ℝ) :
    1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)
      = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ)
        * (Complex.cos ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ)
          + Complex.sin ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * I) := by
  have h1 : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    linarith [one_sub_cos_two_pi_mul x]
  have h2 : Real.sin (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.sin_two_mul]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, h1, h2]
  push_cast
  ring

/-- `‖1 − e^{2πix}‖ = 2 sin(πx)` for `x ∈ (0,1)` (`hx`): the polar form `one_sub_exp_eq`, the
unit modulus of `cos θ + i sin θ`, and `sin_pi_mul_pos` for the sign of the modulus. Consumed
here by `exp_ne_one`, `abs_sum_sin_le`, `abs_sum_cos_le` and the sawtooth value (§4), and across
`Salt/` by `EvenChiFourier` and `EvenChiSine` (the modulus of `1 − ζ^a` at `a/q ∈ (0,1)`). -/
theorem norm_one_sub_exp (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ‖1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)‖ = 2 * Real.sin (Real.pi * x) := by
  rw [one_sub_exp_eq x, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith [sin_pi_mul_pos hx])]

/-- `e^{2πix} ≠ 1` for `x ∈ (0,1)` (`hx`): were it `1`, `norm_one_sub_exp` would read
`0 = 2 sin(πx)` against `sin_pi_mul_pos`. The `z ≠ 1` the geometric sums of `abs_sum_sin_le` and
`abs_sum_cos_le` divide by; in-file consumers only. -/
theorem exp_ne_one (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) ≠ 1 := by
  intro h
  have hn := norm_one_sub_exp hx
  rw [h, sub_self, norm_zero] at hn
  linarith [sin_pi_mul_pos hx]

/-- **The partial sums of `sin (2πnx)` are bounded**, uniformly in `N`. -/
theorem abs_sum_sin_le (hx : x ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    |∑ n ∈ range N, Real.sin (2 * Real.pi * x * n)| ≤ 1 / Real.sin (Real.pi * x) := by
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hzne : z ≠ 1 := exp_ne_one hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have heq : ∑ n ∈ range N, Real.sin (2 * Real.pi * x * n) = (∑ n ∈ range N, z ^ n).im := by
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun n _ => (exp_pow_im x n).symm
  rw [heq]
  refine le_trans (Complex.abs_im_le_norm _) ?_
  rw [geom_sum_eq hzne, norm_div]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, hnz, one_pow, norm_one]
    norm_num
  have hden : ‖z - 1‖ = 2 * Real.sin (Real.pi * x) := by
    rw [← norm_neg, neg_sub]
    exact norm_one_sub_exp hx
  rw [hden, div_le_div_iff₀ (by linarith) hsin]
  nlinarith only [hsin, hnum]

/-- The `n`-th power of `e^{2πix}` has real part `cos (2πnx)`. -/
theorem exp_pow_re (x : ℝ) (n : ℕ) :
    ((Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)) ^ n).re
      = Real.cos (2 * Real.pi * x * n) := by
  rw [← Complex.exp_nat_mul,
    show ((n : ℂ) * (((2 * Real.pi * x : ℝ) : ℂ) * I))
      = (((2 * Real.pi * x * n : ℝ) : ℂ)) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- **The partial sums of `cos (2πnx)` are bounded**, uniformly in `N`. -/
theorem abs_sum_cos_le (hx : x ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    |∑ n ∈ range N, Real.cos (2 * Real.pi * x * n)| ≤ 1 / Real.sin (Real.pi * x) := by
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hzne : z ≠ 1 := exp_ne_one hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have heq : ∑ n ∈ range N, Real.cos (2 * Real.pi * x * n)
      = (∑ n ∈ range N, z ^ n).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => (exp_pow_re x n).symm
  rw [heq]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [geom_sum_eq hzne, norm_div]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, hnz, one_pow, norm_one]
    norm_num
  have hden : ‖z - 1‖ = 2 * Real.sin (Real.pi * x) := by
    rw [← norm_neg, neg_sub]
    exact norm_one_sub_exp hx
  rw [hden, div_le_div_iff₀ (by linarith) hsin]
  nlinarith only [hsin, hnum]


end Geometry

/-! ## §4 — the sawtooth Fourier series -/

/-- **The sawtooth Fourier series** `∑_{n ≥ 1} sin (2πnx) / n = π (1/2 − x)` on `(0,1)`, stated as
a limit of partial sums: the series is only conditionally convergent, so this is deliberately NOT
a `tsum` statement. -/
theorem tendsto_sum_sin_div_nat {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun N => ∑ n ∈ range N, Real.sin (2 * Real.pi * x * n) / n) atTop
      (𝓝 (Real.pi * (1 / 2 - x))) := by
  set c : ℕ → ℝ := fun n => Real.sin (2 * Real.pi * x * n) with hc
  set f : ℕ → ℝ := fun n => c n / n with hf
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  -- Step 1: convergence, by Dirichlet's test.
  have hbdd : ∀ n : ℕ, ‖∑ i ∈ range n, c (i + 1)‖ ≤ 1 / Real.sin (Real.pi * x) := by
    intro n
    have h : ∑ i ∈ range n, c (i + 1) = ∑ i ∈ range (n + 1), c i := by
      rw [Finset.sum_range_succ' c n]
      simp [hc]
    rw [Real.norm_eq_abs, h]
    exact abs_sum_sin_le hx (n + 1)
  have hanti : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    simp only [one_div]
    exact inv_anti₀ (by positivity) hij'
  have hzero : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hbdd
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hcauchy
  simp only [smul_eq_mul] at hT
  have hTf : Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 T) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    refine hT.congr fun N => ?_
    rw [Finset.sum_range_succ' f N]
    have h0 : f 0 = 0 := by simp [hf, hc]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    push_cast
    ring
  -- Step 2: Abel's limit theorem transfers the value from the power series.
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hTf
  have hval : ∀ r : ℝ, |r| < 1 →
      ∑' n : ℕ, f n * r ^ n = -(Complex.log (1 - (r : ℂ) * z)).im := by
    intro r hr
    have hnorm : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, hnz, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hr
    have H2 := Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hnorm)
    have hcongr : ∀ n : ℕ, (((r : ℂ) * z) ^ n / (n : ℂ)).im = f n * r ^ n := by
      intro n
      have e : ((r : ℂ) * z) ^ n / (n : ℂ) = (((r ^ n / n : ℝ)) : ℂ) * z ^ n := by
        push_cast
        ring
      rw [e, Complex.im_ofReal_mul, exp_pow_im x n]
      simp only [hf, hc]
      ring
    have H3 : HasSum (fun n : ℕ => f n * r ^ n) (-(Complex.log (1 - (r : ℂ) * z))).im :=
      H2.congr_fun fun n => (hcongr n).symm
    rw [H3.tsum_eq, Complex.neg_im]
  have heventually : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∑' n : ℕ, f n * r ^ n = -(Complex.log (1 - (r : ℂ) * z)).im := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), -1 < r :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
    filter_upwards [h1, h2] with r hr1 hr2
    exact hval r (abs_lt.mpr ⟨hr2, hr1⟩)
  have habel' : Tendsto (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).im) (𝓝[<] (1 : ℝ)) (𝓝 T) :=
    habel.congr' heventually
  -- Step 3: the limit of the right-hand side, by continuity of `log` at `1 − z`.
  have hpolar : 1 - z = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ)
      * (Complex.cos ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ)
        + Complex.sin ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * I) := one_sub_exp_eq x
  have hre : (1 - z).re = 1 - Real.cos (2 * Real.pi * x) := by
    rw [hz, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have hslit : (1 - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre, one_sub_cos_two_pi_mul]
    positivity
  have hcont : Tendsto (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).im) (𝓝[<] (1 : ℝ))
      (𝓝 (-(Complex.log (1 - z)).im)) := by
    have h1 : ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ) * z) 1 :=
      continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have h2 : ContinuousAt (fun r : ℝ => Complex.log (1 - (r : ℂ) * z)) 1 := by
      refine h1.clog ?_
      rw [Complex.ofReal_one, one_mul]
      exact hslit
    have h3 : ContinuousAt (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).im) 1 :=
      ContinuousAt.neg (ContinuousAt.comp (g := Complex.im)
        Complex.continuous_im.continuousAt h2)
    have h4 := (h3.continuousWithinAt (s := Set.Iio (1 : ℝ))).tendsto
    rw [Complex.ofReal_one, one_mul] at h4
    exact h4
  -- Step 4: the argument of `1 − z`.
  have harg : (Complex.log (1 - z)).im = Real.pi * x - Real.pi / 2 := by
    rw [Complex.log_im, hpolar]
    refine Complex.arg_mul_cos_add_sin_mul_I (by linarith) (Set.mem_Ioc.mpr ⟨?_, ?_⟩)
    · nlinarith only [Real.pi_pos, hx.1]
    · nlinarith only [Real.pi_pos, hx.2, hx.1]
  have hTval : T = Real.pi * (1 / 2 - x) := by
    have h := tendsto_nhds_unique habel' hcont
    rw [harg] at h
    linarith
  rw [← hTval]
  exact hTf


end WaveTurbulence.NumberTheory.SineSeries

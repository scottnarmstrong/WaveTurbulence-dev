/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.ZExtract

/-!
# Approximate identities with moving integrands (DH21 (approxid))

The regularized pair kernels are `gk θ u = θ⁻¹e^{-πu²/4θ²}` (a variable not in `Z`) and
`hk θ u = -(πu/2θ²)e^{-πu²/4θ²}` (a variable in `Z`). `kk b θ` is `gk θ` for `b = false` and `hk θ` for
`b = true`. On `[0, c]` the kernel `gk θ` has mass `→ 1`, and `hk θ` has mass `→ -1`; this is the F61
sign. Both have first moment `∫_0^c |kk| u du ≤ θ`.

* `tendsto_integral_kk_mul_of_lip`: `∫_0^c kk b θ u · f_θ(u) du → sg b · a`, if `f_θ(0) → a` and
  `|f_θ(u) - f_θ(0)| ≤ L u` uniformly in `θ`.
* `tendsto_integral_kk_tail`: `∫_δ^c kk b θ u · f_θ(u) du → 0` for `δ > 0` and bounded `f_θ`.
* `integral_abs_kk_le`: `∫_a^b |kk b θ u| du ≤ 2`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-- The regularized pair kernel: `gk θ` (`b = false`) or `hk θ` (`b = true`). -/
@[expose] noncomputable def kk (b : Bool) (θ u : ℝ) : ℝ := if b then hk θ u else gk θ u

/-- The one-sided mass of `kk b`: `1` or `-1`. -/
@[expose] def sg (b : Bool) : ℂ := if b then -1 else 1

@[fun_prop] theorem continuous_kk (b : Bool) (θ : ℝ) : Continuous (kk b θ) := by
  unfold kk; split_ifs <;> fun_prop

theorem kk_neg (b : Bool) (θ u : ℝ) : kk b θ (-u) = (if b then -1 else 1) * kk b θ u := by
  unfold kk hk gk
  cases b
  · simp
  · simp only [ite_true, neg_mul, one_mul, even_two, Even.neg_pow]
    ring

theorem abs_kk_of_nonneg {b : Bool} {θ u : ℝ} (hθ : 0 < θ) (hu : 0 ≤ u) :
    |kk b θ u| = if b then -hk θ u else gk θ u := by
  unfold kk
  cases b
  · simp [abs_of_nonneg (gk_nonneg hθ u)]
  · simp only [ite_true]
    rw [abs_of_nonpos (by linarith [neg_hk_nonneg (θ := θ) hu])]

/-! ### Masses and moments -/

theorem exp_sq_eq_mul_gk {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    Real.exp (-π * u ^ 2 / (4 * θ ^ 2)) = θ * gk θ u := by
  unfold gk; field_simp

theorem integral_gk_mul_le {θ : ℝ} (hθ : 0 < θ) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, gk θ u * u ≤ θ := by
  have e : (fun u => gk θ u * u) = fun u => (2 * θ / π) * -hk θ u := by
    funext u; unfold gk hk; field_simp
  rw [e, intervalIntegral.integral_const_mul, integral_neg_hk]
  have h1 : 0 ≤ Real.exp (-π * c ^ 2 / (4 * θ ^ 2)) := (Real.exp_pos _).le
  have h2 : 2 * θ / π ≤ θ := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.two_le_pi]
  have h3 : 0 ≤ 2 * θ / π := by positivity
  nlinarith

theorem integral_neg_hk_mul_le {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ u in (0 : ℝ)..c, -hk θ u * u ≤ θ := by
  set E : ℝ → ℝ := fun u => Real.exp (-π * u ^ 2 / (4 * θ ^ 2)) with hE
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hd : ∀ u, HasDerivAt (fun u => -u * E u) (-E u - u * hk θ u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => -u) (-1) u := (hasDerivAt_id u).neg
    have h2 : HasDerivAt E (hk θ u) u := hasDerivAt_hk θ u
    convert h1.mul h2 using 1
    ring
  have hi : IntervalIntegrable (fun u => -E u - u * hk θ u) volume 0 c :=
    ((hEc.neg).sub (continuous_id.mul (continuous_hk θ))).intervalIntegrable _ _
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  have e : (fun u => -hk θ u * u) = fun u => (-E u - u * hk θ u) + E u := by funext u; ring
  rw [e, intervalIntegral.integral_add hi (hEc.intervalIntegrable _ _), h1]
  have hEint : ∫ u in (0 : ℝ)..c, E u = θ * ∫ u in (0 : ℝ)..c, gk θ u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => exp_sq_eq_mul_gk hθ u
  rw [hEint]
  have h2 := integral_gk_le_one hθ hc
  have h3 : 0 ≤ c * E c := mul_nonneg hc (Real.exp_pos _).le
  simp only [neg_zero, zero_mul, sub_zero]
  nlinarith

/-- **The first moment**: `∫_0^c |kk b θ u| u du ≤ θ`. -/
theorem integral_abs_kk_mul_le {b : Bool} {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ u in (0 : ℝ)..c, |kk b θ u| * u ≤ θ := by
  rw [intervalIntegral.integral_congr (g := fun u => (if b then -hk θ u else gk θ u) * u)
    fun u hu => by
      rw [uIcc_of_le hc] at hu
      simp only; rw [abs_kk_of_nonneg hθ hu.1]]
  cases b
  · simpa using integral_gk_mul_le hθ c
  · simpa using integral_neg_hk_mul_le hθ hc

theorem integral_abs_kk_le_one {b : Bool} {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ u in (0 : ℝ)..c, |kk b θ u| ≤ 1 := by
  rw [intervalIntegral.integral_congr (g := fun u => if b then -hk θ u else gk θ u)
    fun u hu => by
      rw [uIcc_of_le hc] at hu
      exact abs_kk_of_nonneg hθ hu.1]
  cases b
  · simpa using integral_gk_le_one hθ hc
  · simp only [ite_true]
    rw [integral_neg_hk]
    linarith [Real.exp_pos (-π * c ^ 2 / (4 * θ ^ 2))]

theorem abs_kk_neg (b : Bool) (θ u : ℝ) : |kk b θ (-u)| = |kk b θ u| := by
  rw [kk_neg]; cases b <;> simp

/-- `∫_a^b |kk b θ u| du ≤ 2` for `a ≤ b`. -/
theorem integral_abs_kk_le {b : Bool} {θ : ℝ} (hθ : 0 < θ) {a c : ℝ} (hac : a ≤ c) :
    ∫ u in a..c, |kk b θ u| ≤ 2 := by
  have hcont : Continuous fun u => |kk b θ u| := (continuous_kk b θ).abs
  have hnn : ∀ x y : ℝ, x ≤ y → 0 ≤ ∫ u in x..y, |kk b θ u| := fun x y hxy =>
    intervalIntegral.integral_nonneg hxy fun u _ => abs_nonneg _
  have hpos : ∀ y, 0 ≤ y → ∫ u in (0 : ℝ)..y, |kk b θ u| ≤ 1 := fun y hy =>
    integral_abs_kk_le_one hθ hy
  have hneg : ∀ y, y ≤ 0 → ∫ u in y..0, |kk b θ u| ≤ 1 := by
    intro y hy
    have e : ∫ u in y..0, |kk b θ u| = ∫ u in (0 : ℝ)..(-y), |kk b θ u| := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := -y) (fun u => |kk b θ u|)
      simp only [neg_neg, neg_zero] at h
      rw [← h]
      exact intervalIntegral.integral_congr fun u _ => abs_kk_neg b θ u
    rw [e]; exact hpos _ (by linarith)
  rcases le_total c 0 with hc0 | hc0
  · have h2 : ∫ u in a..c, |kk b θ u| ≤ ∫ u in a..0, |kk b θ u| := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := c) (hcont.intervalIntegrable a c)
        (hcont.intervalIntegrable c 0)]
      linarith [hnn c 0 hc0]
    linarith [hneg a (hac.trans hc0)]
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable a 0)
      (hcont.intervalIntegrable 0 c)]
    rcases le_total a 0 with ha0 | ha0
    · linarith [hneg a ha0, hpos c hc0]
    · have h1 : ∫ u in a..0, |kk b θ u| = -∫ u in (0 : ℝ)..a, |kk b θ u| :=
        intervalIntegral.integral_symm _ _
      linarith [hnn 0 a ha0, hpos c hc0]

/-- The mass of `kk b θ` on `[0, c]` tends to `sg b`. -/
theorem tendsto_integral_kk {b : Bool} {c : ℝ} (hc : 0 < c) :
    Tendsto (fun θ => ((∫ u in (0 : ℝ)..c, kk b θ u : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (sg b)) := by
  cases b
  · have := (tendsto_integral_gk hc).ofReal
    simpa [kk, sg] using this
  · have := ((tendsto_integral_neg_hk hc).neg).ofReal
    simp only [kk, sg, ite_true]
    rw [show ((-1 : ℝ) : ℂ) = -1 by push_cast; rfl] at this
    refine this.congr fun θ => ?_
    rw [intervalIntegral.integral_neg, neg_neg]

/-! ### Moving integrands -/

/-- **One-sided approximate identity with a moving, uniformly Lipschitz integrand.** -/
theorem tendsto_integral_kk_mul_of_lip {b : Bool} {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ → ℂ}
    (hf : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ContinuousOn (f θ) (Icc 0 c)) {L : ℝ}
    (hL : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ u ∈ Icc 0 c, ‖f θ u - f θ 0‖ ≤ L * u) {a : ℂ}
    (ha : Tendsto (fun θ => f θ 0) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun θ => ∫ u in (0 : ℝ)..c, (kk b θ u : ℂ) * f θ u) (𝓝[>] 0) (𝓝 (sg b * a)) := by
  have hsplit : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∫ u in (0 : ℝ)..c, (kk b θ u : ℂ) * f θ u =
      ((∫ u in (0 : ℝ)..c, kk b θ u : ℝ) : ℂ) * f θ 0 +
        ∫ u in (0 : ℝ)..c, (kk b θ u : ℂ) * (f θ u - f θ 0) := by
    filter_upwards [hf] with θ hθ
    have hi1 : IntervalIntegrable (fun u => (kk b θ u : ℂ) * f θ 0) volume 0 c :=
      ((continuous_ofReal.comp (continuous_kk b θ)).mul continuous_const).intervalIntegrable _ _
    have hcont : ContinuousOn (fun u => (kk b θ u : ℂ) * f θ u) (uIcc 0 c) := by
      rw [uIcc_of_le hc.le]
      exact (continuous_ofReal.comp (continuous_kk b θ)).continuousOn.mul hθ
    have hi2 : IntervalIntegrable (fun u => (kk b θ u : ℂ) * (f θ u - f θ 0)) volume 0 c := by
      refine (hcont.intervalIntegrable).sub hi1 |>.congr ?_
      intro u _; simp only; ring
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_add hi1 hi2]
    exact intervalIntegral.integral_congr fun u _ => by ring
  refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
  rw [show sg b * a = sg b * a + 0 by ring]
  refine ((tendsto_integral_kk hc).mul ha).add ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlin : Tendsto (fun θ : ℝ => max L 0 * θ) (𝓝[>] 0) (𝓝 0) := by
    have hc0 : Continuous fun θ : ℝ => max L 0 * θ := continuous_const.mul continuous_id
    have := (hc0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [mul_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun θ => norm_nonneg _) ?_ hlin
  filter_upwards [hL, eventually_pos_nhdsGT] with θ hθL hθ
  calc ‖∫ u in (0 : ℝ)..c, (kk b θ u : ℂ) * (f θ u - f θ 0)‖
      ≤ ∫ u in (0 : ℝ)..c, max L 0 * (|kk b θ u| * u) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hc.le
          (Eventually.of_forall fun u hu => ?_) ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have := hθL u ⟨hu.1.le, hu.2⟩
          calc |kk b θ u| * ‖f θ u - f θ 0‖ ≤ |kk b θ u| * (max L 0 * u) :=
                mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_right
                  (le_max_left _ _) hu.1.le)) (abs_nonneg _)
            _ = max L 0 * (|kk b θ u| * u) := by ring
        · exact (((continuous_kk b θ).abs.mul continuous_id).const_mul _).intervalIntegrable _ _
    _ = max L 0 * ∫ u in (0 : ℝ)..c, |kk b θ u| * u := intervalIntegral.integral_const_mul _ _
    _ ≤ max L 0 * θ := mul_le_mul_of_nonneg_left (integral_abs_kk_mul_le hθ hc.le) (le_max_right _ _)

/-- **The tail of the kernel**: `∫_δ^c kk b θ u · f_θ(u) du → 0` for `δ > 0` and bounded `f_θ`. -/
theorem tendsto_integral_kk_tail {b : Bool} {δ c : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c) {f : ℝ → ℝ → ℂ}
    {M : ℝ}
    (hM : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ u ∈ Icc δ c, ‖f θ u‖ ≤ M) :
    Tendsto (fun θ => ∫ u in δ..c, (kk b θ u : ℂ) * f θ u) (𝓝[>] 0) (𝓝 0) := by
  have hc : 0 < c := hδ.trans_le hδc
  have htail : Tendsto (fun θ => ∫ u in δ..c, |kk b θ u|) (𝓝[>] 0) (𝓝 0) := by
    cases b
    · refine (tendsto_integral_gk_tail hδ hc).congr' ?_
      filter_upwards [eventually_pos_nhdsGT] with θ hθ
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hδc] at hu
      simp [kk, abs_of_nonneg (gk_nonneg hθ u)]
    · refine (tendsto_integral_neg_hk_tail hδ hc).congr' ?_
      filter_upwards [eventually_pos_nhdsGT] with θ hθ
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hδc] at hu
      exact (abs_kk_of_nonneg (b := true) hθ (hδ.le.trans hu.1)).symm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 := htail.const_mul (max M 0)
  rw [mul_zero] at h2
  refine squeeze_zero' (Eventually.of_forall fun θ => norm_nonneg _) ?_ h2
  filter_upwards [hM] with θ hθ
  calc ‖∫ u in δ..c, (kk b θ u : ℂ) * f θ u‖ ≤ ∫ u in δ..c, max M 0 * |kk b θ u| := by
        refine intervalIntegral.norm_integral_le_of_norm_le hδc
          (Eventually.of_forall fun u hu => ?_) ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right ((hθ u ⟨hu.1.le, hu.2⟩).trans (le_max_left _ _))
            (abs_nonneg _)
        · exact ((continuous_kk b θ).abs.const_mul _).intervalIntegrable _ _
    _ = max M 0 * ∫ u in δ..c, |kk b θ u| := intervalIntegral.integral_const_mul _ _

end WaveTurbulence.Cancel

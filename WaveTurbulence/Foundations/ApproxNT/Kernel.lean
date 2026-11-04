/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Chi0
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
public import WaveTurbulence.Foundations.NTSP.Lemma67Slices

/-!
# The truncated principal-value kernel `χ_∞(u)/u` and its Fourier transform (packet NT6)

The factors `χ_∞(Ω_j)/Ω_j`, `j ∈ J`, of DH23 Prop 6.4 are not integrable at infinity. On a bounded
range `|u| ≤ 2^K` we replace `χ_∞(u)/u` by the finite dyadic sum

`m_K(u) = ∑_{k ≤ K} 2^{-k} ψ(2^{-k} u)`, `ψ(u) = (χ₀(u/2) - χ₀(u))/u`,

which equals `(χ₀(2^{-K-1}u) - χ₀(u))/u`. Here `ψ` is a fixed odd smooth compactly supported
function, so `ψ̂(0) = 0`, `|ψ̂(t)| ≲ min(|t|, |t|⁻¹)` and `|t|^{2d} |ψ̂(t)| ≲ 1`. The Fourier transform
`m̂_K(σ) = ∑_{k ≤ K} ψ̂(2^k σ)` therefore satisfies `|m̂_K(σ)| ⟨σ⟩^{2d} ≤ M_d` uniformly in `K`
(this is the cancellation of the principal value, in Fourier variables).
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped SchwartzMap ContDiff FourierTransform

namespace WaveTurbulence.ApproxNT

/-- The dyadic piece `ψ(u) = (χ₀(u/2) - χ₀(u))/u`. -/
@[expose] def psiKer (u : ℝ) : ℝ := (Fourier.chi0 (u / 2) - Fourier.chi0 u) / u

theorem psiKer_eq_zero_of_small {u : ℝ} (hu : |u| ≤ 1 / 2) : psiKer u = 0 := by
  rw [psiKer, Fourier.chi0_eq_one hu, Fourier.chi0_eq_one, sub_self, zero_div]
  rw [abs_div, abs_two]; linarith [abs_nonneg u]

theorem psiKer_eq_zero_of_large {u : ℝ} (hu : 2 ≤ |u|) : psiKer u = 0 := by
  rw [psiKer, Fourier.chi0_eq_zero, Fourier.chi0_eq_zero, sub_self, zero_div]
  · linarith
  · rw [abs_div, abs_two]; linarith

theorem psiKer_neg (u : ℝ) : psiKer (-u) = -psiKer u := by
  rw [psiKer, psiKer, neg_div, Fourier.chi0_even, Fourier.chi0_even, div_neg]

theorem contDiff_psiKer : ContDiff ℝ ∞ psiKer := by
  rw [contDiff_iff_contDiffAt]
  intro u₀
  by_cases h0 : u₀ = 0
  · subst h0
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hu
    exact psiKer_eq_zero_of_small hu.le
  · have hn : ContDiff ℝ ∞ (fun u : ℝ => Fourier.chi0 (u / 2) - Fourier.chi0 u) :=
      (Fourier.chi0_contDiff.comp (contDiff_id.div_const 2)).sub Fourier.chi0_contDiff
    exact hn.contDiffAt.div contDiffAt_id h0

theorem hasCompactSupport_psiKer : HasCompactSupport psiKer := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2) ?_
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  exact hu (psiKer_eq_zero_of_large (not_le.mp h).le)

/-- The dyadic piece as a complex Schwartz function. -/
@[expose] def psiS : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_psiKer.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp contDiff_psiKer)

theorem psiS_apply (u : ℝ) : psiS u = (psiKer u : ℂ) := rfl

/-- Its Fourier transform `ψ̂`. -/
@[expose] def psiHat : 𝓢(ℝ, ℂ) := 𝓕 psiS

theorem psiHat_apply (t : ℝ) : psiHat t = 𝓕 (psiS : ℝ → ℂ) t := by
  rw [psiHat, SchwartzMap.fourier_coe]

theorem integral_psiS : ∫ u, psiS u = 0 := by
  have h : ∫ u, psiS u = ∫ u, psiS (-u) := (integral_neg_eq_self _ _).symm
  simp only [psiS_apply, psiKer_neg, Complex.ofReal_neg, integral_neg] at h
  have h2 : (2 : ℂ) * ∫ u, (psiKer u : ℂ) = 0 := by rw [two_mul]; nth_rw 1 [h]; ring
  simpa [psiS_apply] using h2

theorem psiHat_zero : psiHat 0 = 0 := by
  rw [psiHat_apply, Real.fourier_real_eq]
  simpa using integral_psiS

/-- The first moment of `ψ`. -/
@[expose] def psiMoment : ℝ := ∫ u, |u| * ‖psiS u‖

theorem integrable_moment_psiS : Integrable (fun u : ℝ => |u| * ‖psiS u‖) := by
  have h := psiS.integrable_pow_mul (μ := volume) 1
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [Real.norm_eq_abs]

theorem integrable_fourierChar_smul_psiS (a : ℝ → ℝ) (ha : Continuous a) :
    Integrable (fun v => 𝐞 (a v) • psiS v) := by
  refine psiS.integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((Real.continuous_fourierChar.comp ha).smul psiS.continuous).aestronglyMeasurable
  · rw [Circle.norm_smul]

theorem norm_psiHat_le_mul (t : ℝ) : ‖psiHat t‖ ≤ 2 * Real.pi * psiMoment * |t| := by
  have hsub : psiHat t = psiHat t - psiHat 0 := by rw [psiHat_zero, sub_zero]
  rw [hsub, psiHat_apply, psiHat_apply, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_sub (integrable_fourierChar_smul_psiS _ (by fun_prop))
      (integrable_fourierChar_smul_psiS _ (by fun_prop))]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ v, ‖𝐞 (-(v * t)) • psiS v - 𝐞 (-(v * 0)) • psiS v‖
      ≤ ∫ v, 2 * Real.pi * |t| * (|v| * ‖psiS v‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
          (integrable_moment_psiS.const_mul _) (Filter.Eventually.of_forall fun v => ?_)
        simp only [Circle.smul_def, smul_eq_mul]
        rw [← sub_mul, norm_mul]
        have h := NTSP.norm_fourierChar_sub_le (-(v * t)) (-(v * 0))
        calc ‖(𝐞 (-(v * t)) : ℂ) - 𝐞 (-(v * 0))‖ * ‖psiS v‖
            ≤ (2 * Real.pi * |-(v * t) - -(v * 0)|) * ‖psiS v‖ :=
              mul_le_mul_of_nonneg_right h (norm_nonneg _)
          _ = 2 * Real.pi * |t| * (|v| * ‖psiS v‖) := by
              rw [mul_zero, neg_zero, sub_zero, abs_neg, abs_mul]; ring
    _ = 2 * Real.pi * psiMoment * |t| := by rw [integral_const_mul, psiMoment]; ring

/-- Schwartz decay of `ψ̂`. -/
theorem pow_mul_norm_psiHat_le (k : ℕ) (t : ℝ) :
    |t| ^ k * ‖psiHat t‖ ≤ SchwartzMap.seminorm ℝ k 0 psiHat := by
  have h := psiHat.norm_pow_mul_le_seminorm ℝ k t
  simpa [Real.norm_eq_abs] using h

/-- The constant in `|ψ̂(t)| ≤ a min(|t|, |t|⁻¹)`. -/
@[expose] def psiConstA : ℝ := max (2 * Real.pi * psiMoment) (SchwartzMap.seminorm ℝ 1 0 psiHat)

theorem psiMoment_nonneg : 0 ≤ psiMoment :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem psiConstA_nonneg : 0 ≤ psiConstA :=
  le_max_of_le_left (by have := psiMoment_nonneg; positivity)

theorem norm_psiHat_le_min {t : ℝ} (ht : t ≠ 0) :
    ‖psiHat t‖ ≤ psiConstA * min |t| |t|⁻¹ := by
  have hpos : 0 < |t| := abs_pos.2 ht
  rcases min_cases |t| |t|⁻¹ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · exact (norm_psiHat_le_mul t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
  · have h1 := pow_mul_norm_psiHat_le 1 t
    rw [pow_one] at h1
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact h1.trans (le_max_right _ _)

/-- The dyadic majorant `B(x)` of `∑_k min(2^k x, (2^k x)⁻¹)`. -/
@[expose] def dyadicB (x : ℝ) : ℝ := if x < 1 then 4 - 2 * x else 2 / x

theorem sum_min_dyadic_le_B (K : ℕ) : ∀ x : ℝ, 0 < x →
    ∑ k ∈ range (K + 1), min ((2 : ℝ) ^ k * x) ((2 : ℝ) ^ k * x)⁻¹ ≤ dyadicB x := by
  induction K with
  | zero =>
      intro x hx
      simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul, dyadicB]
      split_ifs with h
      · exact (min_le_left _ _).trans (by linarith)
      · refine (min_le_right _ _).trans ?_
        rw [inv_eq_one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hx.le
  | succ K ih =>
      intro x hx
      rw [sum_range_succ']
      have hrec : ∑ k ∈ range (K + 1), min ((2 : ℝ) ^ (k + 1) * x) ((2 : ℝ) ^ (k + 1) * x)⁻¹ =
          ∑ k ∈ range (K + 1), min ((2 : ℝ) ^ k * (2 * x)) ((2 : ℝ) ^ k * (2 * x))⁻¹ := by
        refine sum_congr rfl fun k _ => ?_
        rw [pow_succ, mul_assoc]
      rw [hrec]
      have h2 := ih (2 * x) (by linarith)
      simp only [pow_zero, one_mul]
      have hB2 : dyadicB (2 * x) = if 2 * x < 1 then 4 - 4 * x else x⁻¹ := by
        unfold dyadicB
        split_ifs
        · ring
        · field_simp
      rw [hB2] at h2
      unfold dyadicB
      by_cases hx1 : x < 1
      · have hinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 hx1.le
        rw [min_eq_left (by linarith)]
        simp only [hx1, ↓reduceIte]
        by_cases hx2 : 2 * x < 1
        · simp only [hx2, ↓reduceIte] at h2; linarith
        · simp only [hx2, ↓reduceIte] at h2
          rw [not_lt] at hx2
          have hxy : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
          have key : x + x⁻¹ ≤ 4 - 2 * x := by
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * x - 1) (by linarith : (0 : ℝ) ≤ 1 - x),
              mul_nonneg hx.le (by linarith : (0 : ℝ) ≤ x⁻¹)]
          linarith
      · rw [not_lt] at hx1
        have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
        have hn1 : ¬ x < 1 := not_lt.2 hx1
        have hn2 : ¬ 2 * x < 1 := by linarith
        rw [min_eq_right (by linarith)]
        simp only [hn1, ↓reduceIte]
        simp only [hn2, ↓reduceIte] at h2
        rw [div_eq_mul_inv]; linarith

theorem dyadicB_le_four {x : ℝ} (hx : 0 < x) : dyadicB x ≤ 4 := by
  unfold dyadicB
  split_ifs with h
  · linarith
  · rw [not_lt] at h
    rw [div_le_iff₀ hx]; linarith

/-- The truncated kernel `m_K(u) = ∑_{k ≤ K} 2^{-k} ψ(2^{-k}u)`. -/
@[expose] def mKer (K : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ range (K + 1), (((2 : ℝ) ^ k)⁻¹ : ℂ) * psiS (u / 2 ^ k)

/-- Its Fourier transform `m̂_K(σ) = ∑_{k ≤ K} ψ̂(2^k σ)`. -/
@[expose] def mKerHat (K : ℕ) (σ : ℝ) : ℂ := ∑ k ∈ range (K + 1), psiHat ((2 : ℝ) ^ k * σ)

/-- On `|u| ≤ 2^K` the truncated kernel is `χ_∞(u)/u`. -/
theorem mKer_eq {K : ℕ} {u : ℝ} (hu : |u| ≤ 2 ^ K) :
    mKer K u = ((Fourier.chiInfinity u / u : ℝ) : ℂ) := by
  by_cases h0 : u = 0
  · subst h0
    simp [mKer, psiS_apply, psiKer, Fourier.chiInfinity]
  have hterm : ∀ k ∈ range (K + 1), (((2 : ℝ) ^ k)⁻¹ : ℂ) * psiS (u / 2 ^ k) =
      (((Fourier.chi0 (u / 2 ^ (k + 1)) - Fourier.chi0 (u / 2 ^ k)) / u : ℝ) : ℂ) := by
    intro k _
    have hc : (((2 : ℝ) ^ k)⁻¹ : ℂ) * psiS (u / 2 ^ k) =
        ((((2 : ℝ) ^ k)⁻¹ * psiKer (u / 2 ^ k) : ℝ) : ℂ) := by
      rw [psiS_apply]; push_cast; ring
    rw [hc]
    congr 1
    have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [psiKer, show u / 2 ^ k / 2 = u / 2 ^ (k + 1) by rw [pow_succ, div_div]]
    field_simp
  rw [mKer, sum_congr rfl hterm, ← Complex.ofReal_sum, ← sum_div,
    sum_range_sub (f := fun k => Fourier.chi0 (u / 2 ^ k)) (K + 1)]
  congr 2
  rw [pow_zero, div_one, Fourier.chiInfinity, Fourier.chi0_eq_one]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (K + 1)), div_le_iff₀ (by positivity),
    pow_succ]
  linarith

/-- Fourier inversion for `ψ`. -/
theorem psiS_eq_integral (v : ℝ) : psiS v = ∫ τ, psiHat τ * (𝐞 (τ * v) : ℂ) := by
  have h := Continuous.fourierInv_fourier_eq psiS.continuous psiS.integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 psiS).integrable)
  have h2 := congrFun h v
  rw [Real.fourierInv_eq] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only []
  rw [psiHat_apply, Circle.smul_def, smul_eq_mul, mul_comm]
  simp [mul_comm]

/-- The Fourier representation of the truncated kernel. -/
theorem mKer_eq_integral (K : ℕ) (u : ℝ) :
    mKer K u = ∫ t, mKerHat K t * (𝐞 (t * u) : ℂ) := by
  have hint : ∀ k ∈ range (K + 1), Integrable (fun t : ℝ => psiHat ((2 : ℝ) ^ k * t) *
      (𝐞 (t * u) : ℂ)) := by
    intro k _
    have hi : Integrable (fun t : ℝ => psiHat ((2 : ℝ) ^ k * t)) :=
      (psiHat.integrable).comp_mul_left' (by positivity)
    refine hi.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun t => by
      rw [Circle.norm_coe])
  simp_rw [mKerHat, sum_mul]
  rw [integral_finsetSum _ hint, mKer]
  refine sum_congr rfl fun k _ => ?_
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hc := Measure.integral_comp_mul_left
    (fun τ : ℝ => psiHat τ * (𝐞 (τ * (u / 2 ^ k)) : ℂ)) ((2 : ℝ) ^ k)
  beta_reduce at hc
  have he : ∀ t : ℝ, psiHat ((2 : ℝ) ^ k * t) * (𝐞 ((2 : ℝ) ^ k * t * (u / 2 ^ k)) : ℂ) =
      psiHat ((2 : ℝ) ^ k * t) * (𝐞 (t * u) : ℂ) := by
    intro t; congr 3; field_simp
  simp_rw [he] at hc
  rw [hc, ← psiS_eq_integral, abs_of_pos (inv_pos.2 h2k), Complex.real_smul,
    Complex.ofReal_inv]
  push_cast; ring

theorem one_add_sq_pow_le (d : ℕ) (σ : ℝ) : (1 + σ ^ 2) ^ d ≤ 2 ^ d * (1 + |σ| ^ (2 * d)) := by
  have hy : 0 ≤ σ ^ 2 := sq_nonneg σ
  have h1 : 1 + σ ^ 2 ≤ 2 * max 1 (σ ^ 2) := by
    have := le_max_left 1 (σ ^ 2); have := le_max_right 1 (σ ^ 2); linarith
  calc (1 + σ ^ 2) ^ d ≤ (2 * max 1 (σ ^ 2)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = 2 ^ d * max 1 (σ ^ 2) ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (1 + |σ| ^ (2 * d)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases max_cases 1 (σ ^ 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
        · rw [one_pow]; linarith [pow_nonneg (abs_nonneg σ) (2 * d)]
        · rw [pow_mul, sq_abs]; linarith

/-- The uniform weighted bound of the truncated kernel's Fourier transform. -/
@[expose] def kerConst (d : ℕ) : ℝ :=
  2 ^ d * (4 * psiConstA + 2 * SchwartzMap.seminorm ℝ (2 * d) 0 psiHat)

theorem norm_mKerHat_mul_le {d : ℕ} (hd : 1 ≤ d) (K : ℕ) (σ : ℝ) :
    ‖mKerHat K σ‖ * (1 + σ ^ 2) ^ d ≤ kerConst d := by
  set b := SchwartzMap.seminorm ℝ (2 * d) 0 psiHat
  have hb : 0 ≤ b := apply_nonneg _ _
  have ha := psiConstA_nonneg
  by_cases hσ : σ = 0
  · subst hσ
    have : mKerHat K 0 = 0 := by simp [mKerHat, psiHat_zero]
    rw [this, norm_zero, zero_mul, kerConst]; positivity
  have hpos : 0 < |σ| := abs_pos.2 hσ
  have hA : ‖mKerHat K σ‖ ≤ 4 * psiConstA := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range (K + 1), ‖psiHat ((2 : ℝ) ^ k * σ)‖
        ≤ ∑ k ∈ range (K + 1), psiConstA * min ((2 : ℝ) ^ k * |σ|) ((2 : ℝ) ^ k * |σ|)⁻¹ := by
          refine sum_le_sum fun k _ => ?_
          have h := norm_psiHat_le_min (t := (2 : ℝ) ^ k * σ) (by positivity)
          rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)] at h
      _ = psiConstA * ∑ k ∈ range (K + 1), min ((2 : ℝ) ^ k * |σ|) ((2 : ℝ) ^ k * |σ|)⁻¹ :=
          (mul_sum _ _ _).symm
      _ ≤ psiConstA * 4 := mul_le_mul_of_nonneg_left
          ((sum_min_dyadic_le_B K |σ| hpos).trans (dyadicB_le_four hpos)) ha
      _ = 4 * psiConstA := mul_comm _ _
  have hB : |σ| ^ (2 * d) * ‖mKerHat K σ‖ ≤ 2 * b := by
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [mul_sum]
    calc ∑ k ∈ range (K + 1), |σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖
        ≤ ∑ k ∈ range (K + 1), (1 / 2 : ℝ) ^ k * b := by
          refine sum_le_sum fun k _ => ?_
          have h := pow_mul_norm_psiHat_le (2 * d) ((2 : ℝ) ^ k * σ)
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k), mul_pow] at h
          have hk : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ (2 * d) :=
            le_self_pow₀ (one_le_pow₀ (by norm_num)) (by omega)
          have hX : 0 ≤ |σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖ := by positivity
          have h2k : (0 : ℝ) < 2 ^ k := by positivity
          calc |σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖
              = (|σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖ * 2 ^ k) / 2 ^ k := by field_simp
            _ ≤ (((2 : ℝ) ^ k) ^ (2 * d) * |σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖) / 2 ^ k := by
                refine div_le_div_of_nonneg_right ?_ h2k.le
                calc |σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖ * 2 ^ k
                    ≤ |σ| ^ (2 * d) * ‖psiHat ((2 : ℝ) ^ k * σ)‖ * ((2 : ℝ) ^ k) ^ (2 * d) :=
                      mul_le_mul_of_nonneg_left hk hX
                  _ = _ := by ring
            _ ≤ b / 2 ^ k := by gcongr
            _ = (1 / 2 : ℝ) ^ k * b := by rw [one_div, inv_pow, div_eq_inv_mul]
      _ = b * ∑ k ∈ range (K + 1), (1 / 2 : ℝ) ^ k := by rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ b * 2 := mul_le_mul_of_nonneg_left (by
          rw [geom_sum_eq (by norm_num)]
          have : (0 : ℝ) ≤ (1 / 2) ^ (K + 1) := by positivity
          rw [div_le_iff_of_neg (by norm_num)]
          linarith) hb
      _ = 2 * b := mul_comm _ _
  calc ‖mKerHat K σ‖ * (1 + σ ^ 2) ^ d ≤ ‖mKerHat K σ‖ * (2 ^ d * (1 + |σ| ^ (2 * d))) :=
        mul_le_mul_of_nonneg_left (one_add_sq_pow_le d σ) (norm_nonneg _)
    _ = 2 ^ d * (‖mKerHat K σ‖ + |σ| ^ (2 * d) * ‖mKerHat K σ‖) := by ring
    _ ≤ 2 ^ d * (4 * psiConstA + 2 * b) := by gcongr
    _ = kerConst d := rfl

end WaveTurbulence.ApproxNT

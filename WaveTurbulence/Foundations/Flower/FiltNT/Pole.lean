/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppTools
public import WaveTurbulence.Foundations.ApproxNT.Profile

/-! # FILT-NT: the filtered pole `g_S(u) = χ_∞(u)/u · χ₀(u/S)` and its scale-uniform Fourier decay (o82 Prop 2.1)

For `2^K ≥ S` we have `g_S = m_K · χ₀(·/S)` (`m_K = ApproxNT.mKer K`), so `ĝ_S = ∫ χ̂₀(τ) m̂_K(σ - τ/S) dτ`, and the
weighted bound of `m̂_K` (`ApproxNT.norm_mKerHat_mul_le`) transfers by Peetre's inequality, uniformly in `S ≥ 1`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WaveTurbulence.ApproxNT
open scoped FourierTransform ContDiff SchwartzMap

namespace WaveTurbulence.Flower.FiltNT

/-- The filtered pole as a complex function. -/
def gS (S u : ℝ) : ℂ := ((Fourier.chiInfinity u / u * Fourier.chi0 (u / S) : ℝ) : ℂ)

/-- `χ₀` as a complex Schwartz function. -/
def chiS : 𝓢(ℝ, ℂ) :=
  (Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp Fourier.chi0_contDiff)

theorem chiS_apply (u : ℝ) : chiS u = ((Fourier.chi0 u : ℝ) : ℂ) := rfl

/-- Its Fourier transform. -/
def chiHat : 𝓢(ℝ, ℂ) := 𝓕 chiS

theorem chiS_eq_integral (v : ℝ) : chiS v = ∫ τ, chiHat τ * (𝐞 (τ * v) : ℂ) := by
  have h := Continuous.fourierInv_fourier_eq chiS.continuous chiS.integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 chiS).integrable)
  have h2 := congrFun h v
  rw [Real.fourierInv_eq] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only []
  rw [chiHat, SchwartzMap.fourier_coe, Circle.smul_def, smul_eq_mul, mul_comm]
  simp [mul_comm]

theorem gS_eq_mKer {S : ℝ} (hS : 0 < S) {K : ℕ} (hK : S ≤ 2 ^ K) (u : ℝ) :
    gS S u = mKer K u * (((Fourier.chi0 (u / S) : ℝ)) : ℂ) := by
  by_cases hu : |u| ≤ 2 ^ K
  · rw [mKer_eq hu, gS]; push_cast; ring
  · have h1 : 1 ≤ |u / S| := by
      rw [abs_div, abs_of_pos hS, le_div_iff₀ hS]; linarith [not_le.mp hu]
    rw [Fourier.chi0_eq_zero h1]
    simp [gS, Fourier.chi0_eq_zero h1]

theorem integrable_mKer (K : ℕ) : Integrable (mKer K) := by
  unfold mKer
  refine integrable_finsetSum _ fun k _ => ?_
  have h : Integrable (fun u : ℝ => psiS (u / 2 ^ k)) := by
    have hne : ((2 : ℝ) ^ k)⁻¹ ≠ 0 := by positivity
    have : Integrable (fun u : ℝ => psiS (((2 : ℝ) ^ k)⁻¹ * u)) := psiS.integrable.comp_mul_left' hne
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp [div_eq_inv_mul]
  exact h.const_mul _

theorem fourier_mKerHat (K : ℕ) (v : ℝ) : 𝓕 (mKerHat K) v = mKer K (-v) := by
  rw [Real.fourier_real_eq, mKer_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_comm]
  congr 3
  simp [mul_comm]

theorem fourier_mKer (K : ℕ) (σ : ℝ) : 𝓕 (mKer K) σ = mKerHat K σ := by
  have hrep : mKer K = 𝓕⁻ (mKerHat K) := by
    funext u
    rw [Real.fourierInv_eq, mKer_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    rw [mul_comm]
    congr 3
    simp [RCLike.inner_apply, mul_comm]
  have hint : Integrable (mKerHat K) := integrable_mKerHat (d := 1) le_rfl K
  have h2 : Integrable (𝓕 (mKerHat K)) := by
    have : 𝓕 (mKerHat K) = fun v => mKer K (-v) := funext (fourier_mKerHat K)
    rw [this]; exact (integrable_mKer K).comp_neg
  have := (continuous_mKerHat K).fourier_fourierInv_eq hint h2
  rw [hrep]
  exact congrFun this σ

theorem ecoe_cont {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun x => ((𝐞 (f x) : Circle) : ℂ)) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp hf)

theorem phase_mul (σ τ S u : ℝ) :
    (𝐞 (-(u * σ)) : ℂ) * (𝐞 (τ * (u / S)) : ℂ) = (𝐞 (-(u * (σ - τ / S))) : ℂ) := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem fourier_gS {S : ℝ} (hS : 0 < S) {K : ℕ} (hK : S ≤ 2 ^ K) (σ : ℝ) :
    𝓕 (gS S) σ = ∫ τ, chiHat τ * mKerHat K (σ - τ / S) := by
  have hcm := continuous_mKer K
  have hF : Continuous (fun z : ℝ × ℝ => (𝐞 (-(z.1 * σ)) : ℂ) * (mKer K z.1 *
      (chiHat z.2 * (𝐞 (z.2 * (z.1 / S))) : ℂ))) := by
    have h1 : Continuous (fun z : ℝ × ℝ => (𝐞 (-(z.1 * σ)) : ℂ)) :=
      ecoe_cont (by fun_prop)
    have h2 : Continuous (fun z : ℝ × ℝ => (𝐞 (z.2 * (z.1 / S)) : ℂ)) :=
      ecoe_cont (by fun_prop)
    exact h1.mul ((hcm.comp continuous_fst).mul ((chiHat.continuous.comp continuous_snd).mul h2))
  have hint : Integrable (fun z : ℝ × ℝ => (𝐞 (-(z.1 * σ)) : ℂ) * (mKer K z.1 *
      (chiHat z.2 * (𝐞 (z.2 * (z.1 / S))) : ℂ))) := by
    have hb := ((integrable_mKer K).norm).mul_prod ((chiHat.integrable (μ := volume)).norm)
    refine hb.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simp only [norm_mul, Circle.norm_coe, one_mul, mul_one]
    exact le_rfl
  rw [Real.fourier_real_eq]
  have e1 : ∀ u : ℝ, (𝐞 (-(u * σ)) : Circle) • gS S u =
      ∫ τ, (𝐞 (-(u * σ)) : ℂ) * (mKer K u * (chiHat τ * (𝐞 (τ * (u / S)) : ℂ))) := by
    intro u
    rw [gS_eq_mKer hS hK, ← chiS_apply, chiS_eq_integral, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only []
  rw [← fourier_mKer, Real.fourier_real_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  have h := phase_mul σ τ S u
  linear_combination (mKer K u * chiHat τ) * h

theorem integrable_chiHat_weight (d : ℕ) :
    Integrable (fun τ : ℝ => ‖chiHat τ‖ * (1 + τ ^ 2) ^ d) := by
  have h1 := (chiHat.integrable_pow_mul (volume : Measure ℝ) (2 * d))
  have h2 := (chiHat.integrable (μ := (volume : Measure ℝ))).norm
  have h3 := (h2.add h1).const_mul ((2 : ℝ) ^ d)
  refine h3.mono' (by have := chiHat.continuous; fun_prop) (Filter.Eventually.of_forall fun τ => ?_)
  have := one_add_sq_pow_le d τ
  have hn := norm_nonneg (chiHat τ)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + τ ^ 2) ^ d)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left this hn]

theorem peetre (d : ℕ) (σ a : ℝ) :
    (1 + σ ^ 2) ^ d ≤ 2 ^ d * ((1 + (σ - a) ^ 2) ^ d * (1 + a ^ 2) ^ d) := by
  rw [← mul_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  nlinarith [sq_nonneg (σ - a), sq_nonneg a, mul_nonneg (sq_nonneg (σ - a)) (sq_nonneg a),
    sq_nonneg (σ - 2 * a)]

/-- **FiltPoleFourier**, in the form for `gS`: the scale-uniform weighted Fourier bound. -/
theorem filtPole_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : ℝ, 1 ≤ S → ∀ σ : ℝ, ‖𝓕 (gS S) σ‖ * (1 + σ ^ 2) ^ d ≤ K := by
  have hk : 0 ≤ kerConst d := le_trans (by positivity) (norm_mKerHat_mul_le hd 0 0)
  have hW0 : 0 ≤ ∫ τ : ℝ, ‖chiHat τ‖ * (1 + τ ^ 2) ^ d :=
    integral_nonneg fun τ => by positivity
  refine ⟨2 ^ d * kerConst d * ∫ τ : ℝ, ‖chiHat τ‖ * (1 + τ ^ 2) ^ d, by positivity, ?_⟩
  intro S hS σ
  have hS0 : 0 < S := by linarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt S (one_lt_two (α := ℝ))
  rw [fourier_gS hS0 hK.le σ]
  set c : ℝ := (1 + σ ^ 2) ^ d with hc
  have hc0 : 0 < c := by positivity
  have hG := (integrable_chiHat_weight d).const_mul (2 ^ d * kerConst d)
  have hpt : ∀ τ : ℝ, ‖chiHat τ * mKerHat K (σ - τ / S) * (c : ℂ)‖ ≤
      2 ^ d * kerConst d * (‖chiHat τ‖ * (1 + τ ^ 2) ^ d) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    have hb := norm_mKerHat_mul_le hd K (σ - τ / S)
    have hp := peetre d σ (τ / S)
    have ha : (1 + (τ / S) ^ 2) ^ d ≤ (1 + τ ^ 2) ^ d := by
      refine pow_le_pow_left₀ (by positivity) ?_ d
      have : (τ / S) ^ 2 ≤ τ ^ 2 := by
        rw [div_pow]
        exact div_le_self (sq_nonneg τ) (by nlinarith)
      linarith
    have hn := norm_nonneg (chiHat τ)
    have hm := norm_nonneg (mKerHat K (σ - τ / S))
    calc ‖chiHat τ‖ * ‖mKerHat K (σ - τ / S)‖ * c
        ≤ ‖chiHat τ‖ * ‖mKerHat K (σ - τ / S)‖ *
          (2 ^ d * ((1 + (σ - τ / S) ^ 2) ^ d * (1 + (τ / S) ^ 2) ^ d)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 2 ^ d * ‖chiHat τ‖ * (‖mKerHat K (σ - τ / S)‖ * (1 + (σ - τ / S) ^ 2) ^ d) *
          (1 + (τ / S) ^ 2) ^ d := by ring
      _ ≤ 2 ^ d * ‖chiHat τ‖ * kerConst d * (1 + (τ / S) ^ 2) ^ d := by
          gcongr
      _ ≤ 2 ^ d * ‖chiHat τ‖ * kerConst d * (1 + τ ^ 2) ^ d := by gcongr
      _ = _ := by ring
  have hmeasurable : AEStronglyMeasurable (fun τ : ℝ => chiHat τ * mKerHat K (σ - τ / S) * (c : ℂ)) volume := by
    have := chiHat.continuous
    have := continuous_mKerHat K
    exact (by fun_prop : Continuous fun τ : ℝ => chiHat τ * mKerHat K (σ - τ / S) * (c : ℂ)).aestronglyMeasurable
  have h1 := norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall hpt)
  have h2 : ‖(∫ τ, chiHat τ * mKerHat K (σ - τ / S))‖ * c = ‖∫ τ, chiHat τ * mKerHat K (σ - τ / S) * (c : ℂ)‖ := by
    rw [integral_mul_const, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  rw [h2]
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul]

end WaveTurbulence.Flower.FiltNT

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI6

/-!
# DH21 Lemma 5.6: the kernel of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`, first composition

`kcomp_iker_J_eq`: for a basic class `J` kernel `∫ m(α, γ) J_{ℓ; γ}`, the kernel of
`I_{εα₁} 𝒥` is, on the triangle, the sum of three superpositions of `J` kernels
(DH21 L1047–L1049 with the `χ₀ + χ_∞` split of the inner `E`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section Bounds

/-- The real form of `gM 0`, a uniform integrable bound for `kerM`. -/
@[expose] noncomputable def gr (q : ℝ × ℝ) : ℝ :=
  (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) q.2 * (CkM * AkM ^ 0 *
    (Nat.factorial (2 * 0) : ℝ)) / (1 + |q.1|) ^ 3

theorem gr_nonneg (q : ℝ × ℝ) : 0 ≤ gr q := by
  have := kerM_bound.1
  unfold gr
  refine div_nonneg (mul_nonneg ?_ (by positivity)) (by positivity)
  by_cases h : q.2 ∈ Icc (0 : ℝ) 1 <;> simp [h]

theorem gM_zero_eq (q : ℝ × ℝ) : gM 0 q = ENNReal.ofReal (gr q) := rfl

theorem norm_kerM_le_gr (x : ℝ) (q : ℝ × ℝ) : ‖kerM x q‖ ≤ gr q := by
  have h := enorm_iteratedDeriv_kerM_le_ind 0 x q
  simp only [iteratedDeriv_zero] at h
  have h' : ‖kerM x q‖ₑ ≤ gM 0 q := h.trans (mul_le_of_le_one_left bot_le (ind_le_one _))
  rw [gM_zero_eq, ← ofReal_norm] at h'
  exact (ENNReal.ofReal_le_ofReal_iff (gr_nonneg q)).1 h'

theorem measurable_gr : Measurable gr := by
  unfold gr
  exact (((measurable_const.indicator measurableSet_Icc).comp measurable_snd).mul
    measurable_const).div (by fun_prop)

theorem integrable_gr : Integrable gr := by
  refine ⟨measurable_gr.aestronglyMeasurable, ?_⟩
  have : ∫⁻ q, ‖gr q‖ₑ = ∫⁻ q, gM 0 q := lintegral_congr fun q => by
    rw [gM_zero_eq, ← ofReal_norm, Real.norm_of_nonneg (gr_nonneg q)]
  rw [HasFiniteIntegral, this]
  exact lt_of_le_of_lt (lintegral_gM_le 0) (gev_lt_top _ _ _)

theorem norm_phiR_le (x : ℝ) : ‖phiR x‖ ≤ CPhi := by
  rw [phiR, norm_div]
  calc ‖(chiInvR x : ℂ)‖ / ‖(π : ℂ) * I‖ ≤ ‖(chiInvR x : ℂ)‖ / 1 := by
        gcongr
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
        linarith [Real.two_le_pi]
    _ ≤ CPhi := by rw [div_one]; exact norm_chiInvR_le x

variable {Z : Type*} [MeasureSpace Z] [SFinite (volume : Measure Z)]

omit [SFinite (volume : Measure Z)] in
theorem integrable_mul_kerM {f : Z → ℂ} (hf : Integrable f) {X : Z → ℝ} (hX : Measurable X)
    {J : Z × (ℝ × ℝ) → ℂ} (hJ : AEStronglyMeasurable J) (hJ1 : ∀ p, ‖J p‖ ≤ 1) :
    Integrable fun p : Z × (ℝ × ℝ) => f p.1 * kerM (X p.1) p.2 * J p := by
  have hb : Integrable fun p : Z × (ℝ × ℝ) => ‖f p.1‖ * gr p.2 := by
    rw [Measure.volume_eq_prod]; exact hf.norm.mul_prod integrable_gr
  refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
  · refine (hf.aestronglyMeasurable.comp_quasiMeasurePreserving ?_).mul
      ((measurable_kerM.comp ((hX.comp measurable_fst).prodMk
        measurable_snd)).aestronglyMeasurable) |>.mul hJ
    rw [Measure.volume_eq_prod]; exact Measure.quasiMeasurePreserving_fst
  · rw [norm_mul, norm_mul]
    calc ‖f p.1‖ * ‖kerM (X p.1) p.2‖ * ‖J p‖ ≤ ‖f p.1‖ * gr p.2 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_kerM_le_gr _ _) (norm_nonneg _)) (hJ1 p)
            (norm_nonneg _) (mul_nonneg (norm_nonneg _) (gr_nonneg _))
      _ = ‖f p.1‖ * gr p.2 := mul_one _

theorem integral_mul_integral_kerM {f : Z → ℂ} (hf : Integrable f) {X : Z → ℝ}
    (hX : Measurable X) {J : Z × (ℝ × ℝ) → ℂ} (hJ : AEStronglyMeasurable J)
    (hJ1 : ∀ p, ‖J p‖ ≤ 1) :
    ∫ z, f z * ∫ q, kerM (X z) q * J (z, q) =
      ∫ p : Z × (ℝ × ℝ), f p.1 * kerM (X p.1) p.2 * J p := by
  have hi := integrable_mul_kerM hf hX hJ hJ1
  rw [Measure.volume_eq_prod] at hi
  conv_rhs => rw [Measure.volume_eq_prod, integral_prod _ hi]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only
  ring

end Bounds

section Step1

variable {ι : Type*} [Fintype ι]

/-- The form `y = ℓ + γ₁ + εα₁`. -/
@[expose] def formY (ℓ e : ℝ) (γ : ℝ × ℝ) : ℝ := ℓ + γ.1 + e

/-- The form `x = γ₁ + γ₂ + εα₁`. -/
@[expose] def formX (e : ℝ) (γ : ℝ × ℝ) : ℝ := γ.1 + γ.2 + e

theorem measurable_formY (ℓ e : ℝ) : Measurable (formY ℓ e) := by unfold formY; fun_prop
theorem measurable_formX (e : ℝ) : Measurable (formX e) := by unfold formX; fun_prop

theorem integrable_mul_phiR {f : ℝ × ℝ → ℂ} (hf : Integrable f) {Y : ℝ × ℝ → ℝ}
    (hY : Measurable Y) {J : ℝ × ℝ → ℂ} (hJ : AEStronglyMeasurable J) (hJ1 : ∀ γ, ‖J γ‖ ≤ 1) :
    Integrable fun γ => f γ * phiR (Y γ) * J γ := by
  refine (hf.norm.mul_const CPhi).mono' ?_ (Eventually.of_forall fun γ => ?_)
  · exact (hf.aestronglyMeasurable.mul
      (contDiff_phiR.continuous.measurable.comp hY).aestronglyMeasurable).mul hJ
  · rw [norm_mul, norm_mul]
    calc ‖f γ‖ * ‖phiR (Y γ)‖ * ‖J γ‖ ≤ ‖f γ‖ * CPhi * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_phiR_le _) (norm_nonneg _)) (hJ1 γ)
            (norm_nonneg _) (mul_nonneg (norm_nonneg _) CPhi_nonneg)
      _ = ‖f γ‖ * CPhi := mul_one _

/-- **The first composition `I_{e} 𝒥`** (DH21 L1047–L1049). -/
theorem kcomp_iker_J_eq {θ A N : ℝ} (R : JSym ι) (hR : R.Bound θ A N) (e : ℝ) (α' : ι → ℝ)
    {t v : ℝ} (h0 : 0 ≤ t - v) (h1 : t - v ≤ 1) :
    kcomp (iker e) (R.kernel α') t v =
      sp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => R.m α' w.1 * kerM (formY (bundle R.y α') e w.1) w.2) 0
          (fun w => w.2.1) (fun w => formX e w.1 - w.2.1) t v +
        sp (fun γ => R.m α' γ * phiR (formY (bundle R.y α') e γ)) (bundle R.y α')
          (fun γ => e + γ.1) (fun γ => γ.2) t v -
        sp (fun γ => R.m α' γ * phiR (formY (bundle R.y α') e γ)) 0 (fun _ => 0)
          (fun γ => formX e γ) t v := by
  set ℓ := bundle R.y α'
  have hm := hR.reg.integrable α'
  rw [iker_eq_jker, show R.kernel α' = sp (R.m α') ℓ Prod.fst Prod.snd from rfl,
    kcomp_jker_sp hm _ _ _ _ measurable_fst measurable_snd (by linarith)]
  have key : ∀ γ : ℝ × ℝ, R.m α' γ * kcomp (jker 0 0 e) (jker ℓ γ.1 γ.2) t v =
      (R.m α' γ * ∫ q, kerM (formY ℓ e γ) q * jker 0 q.1 (formX e γ - q.1) t v) +
        R.m α' γ * phiR (formY ℓ e γ) * jker ℓ (e + γ.1) γ.2 t v -
        R.m α' γ * phiR (formY ℓ e γ) * jker 0 0 (formX e γ) t v := fun γ => by
    rw [kcomp_jker_split _ _ _ _ _ _ h0 h1]
    have e1 : ℓ - 0 + e + γ.1 = formY ℓ e γ := by simp only [formY]; ring
    have e2 : e + γ.1 + γ.2 = formX e γ := by simp only [formX]; ring
    simp only [e1, e2, zero_add]
    ring
  simp_rw [key]
  have hJa : AEStronglyMeasurable fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      jker 0 p.2.1 (formX e p.1 - p.2.1) t v :=
    ((continuous_jker_coeff 0 t v).measurable.comp ((measurable_fst.comp measurable_snd).prodMk
      (((measurable_formX e).comp measurable_fst).sub
        (measurable_fst.comp measurable_snd)))).aestronglyMeasurable
  have hia := integrable_mul_kerM hm (measurable_formY ℓ e) hJa (fun p => (norm_jker _ _ _ _ _).le)
  have hT1 : Integrable fun γ : ℝ × ℝ =>
      R.m α' γ * ∫ q, kerM (formY ℓ e γ) q * jker 0 q.1 (formX e γ - q.1) t v := by
    have := (by rw [Measure.volume_eq_prod] at hia; exact hia.integral_prod_left :
      Integrable fun γ : ℝ × ℝ => ∫ q, R.m α' γ * kerM (formY ℓ e γ) q *
        jker 0 q.1 (formX e γ - q.1) t v)
    refine this.congr (Eventually.of_forall fun γ => ?_)
    simp only
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun q => by simp only; ring)
  have hJb : AEStronglyMeasurable fun γ : ℝ × ℝ => jker ℓ (e + γ.1) γ.2 t v :=
    ((continuous_jker_coeff ℓ t v).measurable.comp ((measurable_const.add measurable_fst).prodMk
      measurable_snd)).aestronglyMeasurable
  have hJc : AEStronglyMeasurable fun γ : ℝ × ℝ => jker 0 0 (formX e γ) t v :=
    ((continuous_jker_coeff 0 t v).measurable.comp (measurable_const.prodMk
      (measurable_formX e))).aestronglyMeasurable
  have hT2 := integrable_mul_phiR hm (measurable_formY ℓ e) hJb (fun γ => (norm_jker _ _ _ _ _).le)
  have hT3 := integrable_mul_phiR hm (measurable_formY ℓ e) hJc (fun γ => (norm_jker _ _ _ _ _).le)
  have hT12 : Integrable fun γ : ℝ × ℝ =>
      (R.m α' γ * ∫ q, kerM (formY ℓ e γ) q * jker 0 q.1 (formX e γ - q.1) t v) +
        R.m α' γ * phiR (formY ℓ e γ) * jker ℓ (e + γ.1) γ.2 t v := hT1.add hT2
  rw [integral_sub hT12 hT3, integral_add hT1 hT2,
    integral_mul_integral_kerM hm (measurable_formY ℓ e) hJa (fun p => (norm_jker _ _ _ _ _).le)]
  rfl

end Step1

end WaveTurbulence.ClassJR

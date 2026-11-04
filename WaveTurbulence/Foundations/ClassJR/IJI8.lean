/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI7

/-!
# DH21 Lemma 5.6: the kernel of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`, second composition

`kcomp_sp_iker_split`: composing a superposition `∫ f J_{L; u, v}` with `J_{0;0,b}` and splitting
with `χ₀ + χ_∞` gives a `kerM` superposition and two `Φ` terms. `kcomp_IJI_eq` combines this with
`kcomp_iker_J_eq`: the kernel of `I_{εα₁} 𝒥 I_{μ-εα₁}` is the sum of the nine terms of DH21 L1053.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section Split

variable {Z : Type*} [MeasureSpace Z] [SFinite (volume : Measure Z)]

omit [SFinite (volume : Measure Z)] in
theorem integrable_mul_phiR_gen {f : Z → ℂ} (hf : Integrable f) {Y : Z → ℝ}
    (hY : Measurable Y) {J : Z → ℂ} (hJ : AEStronglyMeasurable J) (hJ1 : ∀ z, ‖J z‖ ≤ 1) :
    Integrable fun z => f z * phiR (Y z) * J z := by
  refine (hf.norm.mul_const CPhi).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (hf.aestronglyMeasurable.mul
      (contDiff_phiR.continuous.measurable.comp hY).aestronglyMeasurable).mul hJ
  · rw [norm_mul, norm_mul]
    calc ‖f z‖ * ‖phiR (Y z)‖ * ‖J z‖ ≤ ‖f z‖ * CPhi * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_phiR_le _) (norm_nonneg _)) (hJ1 z)
            (norm_nonneg _) (mul_nonneg (norm_nonneg _) CPhi_nonneg)
      _ = ‖f z‖ * CPhi := mul_one _

/-- **Composition of a superposition with `J_{0;0,b}`, split** (DH21 L1050–L1053). -/
theorem kcomp_sp_iker_split {f : Z → ℂ} (hf : Integrable f) (L : ℝ) {u v : Z → ℝ}
    (hu : Measurable u) (hv : Measurable v) (b : ℝ) {t s : ℝ} (h0 : 0 ≤ t - s)
    (h1 : t - s ≤ 1) :
    kcomp (sp f L u v) (jker 0 0 b) t s =
      (∫ p : Z × (ℝ × ℝ), f p.1 * kerM (v p.1 - L) p.2 *
          jker L (u p.1 + p.2.1) (v p.1 + b - p.2.1) t s) +
        (∫ z, f z * phiR (v z - L) * jker 0 (u z + v z) b t s) -
        ∫ z, f z * phiR (v z - L) * jker L (u z) (v z + b) t s := by
  rw [kcomp_sp_jker hf L 0 0 b hu hv (by linarith)]
  have key : ∀ z, f z * kcomp (jker L (u z) (v z)) (jker 0 0 b) t s =
      (f z * ∫ q, kerM (v z - L) q * jker L (u z + q.1) (v z + b - q.1) t s) +
        f z * phiR (v z - L) * jker 0 (u z + v z) b t s -
        f z * phiR (v z - L) * jker L (u z) (v z + b) t s := fun z => by
    rw [kcomp_jker_split _ _ _ _ _ _ h0 h1]
    have e1 : (0 : ℝ) - L + v z + 0 = v z - L := by ring
    have e2 : u z + v z + 0 = u z + v z := by ring
    have e3 : v z + 0 + b = v z + b := by ring
    have e4 : ∀ q : ℝ × ℝ, v z + 0 + b - q.1 = v z + b - q.1 := fun q => by ring
    simp only [e1, e2, e3]
    ring
  simp_rw [key]
  have hJa : AEStronglyMeasurable fun p : Z × (ℝ × ℝ) =>
      jker L (u p.1 + p.2.1) (v p.1 + b - p.2.1) t s :=
    ((continuous_jker_coeff L t s).measurable.comp (((hu.comp measurable_fst).add
      (measurable_fst.comp measurable_snd)).prodMk (((hv.comp measurable_fst).add
        measurable_const).sub (measurable_fst.comp measurable_snd)))).aestronglyMeasurable
  have hX : Measurable fun z => v z - L := hv.sub measurable_const
  have hia := integrable_mul_kerM hf hX hJa (fun p => (norm_jker _ _ _ _ _).le)
  have hT1 : Integrable fun z =>
      f z * ∫ q, kerM (v z - L) q * jker L (u z + q.1) (v z + b - q.1) t s := by
    have := (by rw [Measure.volume_eq_prod] at hia; exact hia.integral_prod_left :
      Integrable fun z => ∫ q, f z * kerM (v z - L) q * jker L (u z + q.1) (v z + b - q.1) t s)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun q => by simp only; ring)
  have hJb : AEStronglyMeasurable fun z => jker 0 (u z + v z) b t s :=
    ((continuous_jker_coeff 0 t s).measurable.comp ((hu.add hv).prodMk
      measurable_const)).aestronglyMeasurable
  have hJc : AEStronglyMeasurable fun z => jker L (u z) (v z + b) t s :=
    ((continuous_jker_coeff L t s).measurable.comp (hu.prodMk
      (hv.add measurable_const))).aestronglyMeasurable
  have hT2 := integrable_mul_phiR_gen hf hX hJb (fun z => (norm_jker _ _ _ _ _).le)
  have hT3 := integrable_mul_phiR_gen hf hX hJc (fun z => (norm_jker _ _ _ _ _).le)
  have hT12 : Integrable fun z =>
      (f z * ∫ q, kerM (v z - L) q * jker L (u z + q.1) (v z + b - q.1) t s) +
        f z * phiR (v z - L) * jker 0 (u z + v z) b t s := hT1.add hT2
  rw [integral_sub hT12 hT3, integral_add hT1 hT2,
    integral_mul_integral_kerM hf hX hJa (fun p => (norm_jker _ _ _ _ _).le)]

end Split

section Identity

variable {ι : Type*} [Fintype ι]

theorem integrable_fa {θ A N : ℝ} {R : JSym ι} (hR : R.Bound θ A N) (α' : ι → ℝ) (ℓ e : ℝ) :
    Integrable fun w : (ℝ × ℝ) × (ℝ × ℝ) => R.m α' w.1 * kerM (formY ℓ e w.1) w.2 := by
  have := integrable_mul_kerM (hR.reg.integrable α') (measurable_formY ℓ e)
    (J := fun _ => (1 : ℂ)) aestronglyMeasurable_const (fun _ => by simp)
  simpa using this

theorem integrable_fb {θ A N : ℝ} {R : JSym ι} (hR : R.Bound θ A N) (α' : ι → ℝ) (ℓ e : ℝ) :
    Integrable fun γ : ℝ × ℝ => R.m α' γ * phiR (formY ℓ e γ) := by
  have := integrable_mul_phiR (hR.reg.integrable α') (measurable_formY ℓ e)
    (J := fun _ => (1 : ℂ)) aestronglyMeasurable_const (fun _ => by simp)
  simpa using this

/-- **The kernel of `I_e 𝒥 I_b`** as three compositions of superpositions with `J_{0;0,b}`. -/
theorem kcomp_IJI_eq {θ A N : ℝ} (R : JSym ι) (hR : R.Bound θ A N) (e b : ℝ) (α' : ι → ℝ)
    {t s : ℝ} (h0 : 0 ≤ t - s) (h1 : t - s ≤ 1) :
    kcomp (kcomp (iker e) (R.kernel α')) (iker b) t s =
      kcomp (sp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => R.m α' w.1 * kerM (formY (bundle R.y α') e w.1)
          w.2) 0 (fun w => w.2.1) (fun w => formX e w.1 - w.2.1)) (jker 0 0 b) t s +
        kcomp (sp (fun γ => R.m α' γ * phiR (formY (bundle R.y α') e γ)) (bundle R.y α')
          (fun γ => e + γ.1) (fun γ => γ.2)) (jker 0 0 b) t s -
        kcomp (sp (fun γ => R.m α' γ * phiR (formY (bundle R.y α') e γ)) 0 (fun _ => 0)
          (fun γ => formX e γ)) (jker 0 0 b) t s := by
  set ℓ := bundle R.y α'
  have hK : kcomp (kcomp (iker e) (R.kernel α')) (iker b) t s =
      kcomp (fun t z =>
        sp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => R.m α' w.1 * kerM (formY ℓ e w.1) w.2) 0
            (fun w => w.2.1) (fun w => formX e w.1 - w.2.1) t z +
          sp (fun γ => R.m α' γ * phiR (formY ℓ e γ)) ℓ (fun γ => e + γ.1) (fun γ => γ.2) t z -
          sp (fun γ => R.m α' γ * phiR (formY ℓ e γ)) 0 (fun _ => 0) (fun γ => formX e γ) t z)
        (jker 0 0 b) t s := by
    show (∫ z in s..t, kcomp (iker e) (R.kernel α') t z * iker b z s) = ∫ z in s..t, _
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [Set.uIcc_of_le (by linarith)] at hz
    simp only
    rw [kcomp_iker_J_eq R hR e α' (by linarith [hz.2]) (by linarith [hz.1]), iker_eq_jker]
  have hva : Measurable fun w : (ℝ × ℝ) × (ℝ × ℝ) => formX e w.1 - w.2.1 :=
    ((measurable_formX e).comp measurable_fst).sub (measurable_fst.comp measurable_snd)
  have hub : Measurable fun γ : ℝ × ℝ => e + γ.1 := measurable_const.add measurable_fst
  rw [hK, kcomp_add_sub
    (continuous_sp (integrable_fa hR α' ℓ e) 0 (u := fun w => w.2.1)
      (measurable_fst.comp measurable_snd) hva)
    (continuous_sp (integrable_fb hR α' ℓ e) ℓ (u := fun γ => e + γ.1) (v := fun γ => γ.2) hub
      measurable_snd)
    (continuous_sp (integrable_fb hR α' ℓ e) 0 (u := fun _ => 0) (v := fun γ => formX e γ)
      measurable_const (measurable_formX e))
    (continuous_jker 0 0 b)]

end Identity

end WaveTurbulence.ClassJR

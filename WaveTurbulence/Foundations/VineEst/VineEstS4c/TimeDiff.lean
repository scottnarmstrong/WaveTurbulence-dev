/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffNorm
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (c): the time-difference extraction lemma (F2)

Stage two: the parameter integral `H = ∫ Fa` and its `𝔛^θ(ℝ³)` bound by Minkowski.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Real Complex Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.VineEstS4c.TimeDiff

open WaveTurbulence.Fourier

instance : SFinite μα := by unfold μα; infer_instance

theorem continuous_Tk_joint {κ : (Fin 3 → ℝ) → ℂ} (hκ : Continuous κ) :
    Continuous (fun p : ℝ × (Fin 2 → ℝ) × (Fin 3 → ℝ) => Tk κ p.1 (p.2.1 0) (p.2.1 1) p.2.2) := by
  unfold Tk
  have h1 : Continuous (fun p : ℝ × (Fin 2 → ℝ) × (Fin 3 → ℝ) => κ p.2.2) :=
    hκ.comp (continuous_snd.comp continuous_snd)
  fun_prop

theorem Fa_eq_zero {V : Type*} {κ : (Fin 3 → ℝ) → ℂ} {b : ℝ} {G₀ : (Fin 2 → ℝ) → V → ℂ}
    {a : ℝ × (Fin 2 → ℝ)} {τ : Fin 3 → ℝ} (v : V) (h : κ τ = 0) : Fa κ b G₀ a τ v = 0 := by
  simp [Fa, Tk, h]

theorem continuous_Fa_tau {V : Type*} {κ : (Fin 3 → ℝ) → ℂ} (hκ : Continuous κ) (b : ℝ)
    (G₀ : (Fin 2 → ℝ) → V → ℂ) (a : ℝ × (Fin 2 → ℝ)) (v : V) :
    Continuous (fun τ => Fa κ b G₀ a τ v) := by
  unfold Fa
  exact continuous_const.mul (continuous_const.mul (continuous_Tk hκ _ _ _))

theorem integrable_Fa_tau {V : Type*} {κ : (Fin 3 → ℝ) → ℂ} (hκc : HasCompactSupport κ)
    (hκ : Continuous κ) (b : ℝ) (G₀ : (Fin 2 → ℝ) → V → ℂ) (a : ℝ × (Fin 2 → ℝ)) (v : V) :
    Integrable (fun τ => Fa κ b G₀ a τ v) := by
  apply (continuous_Fa_tau hκ b G₀ a v).integrable_of_hasCompactSupport
  exact hκc.mono' (fun τ hτ => by
    by_contra h
    exact hτ (Fa_eq_zero v (by
      by_contra hk
      exact h (subset_tsupport _ hk))))


theorem measurable_Fa {V : Type*} {κ : (Fin 3 → ℝ) → ℂ} (hκ : Continuous κ) (b : ℝ)
    (G₀ : (Fin 2 → ℝ) → V → ℂ) (hG : ∀ v, Integrable (fun t => G₀ t v)) (v : V) :
    Measurable (fun p : (ℝ × (Fin 2 → ℝ)) × (Fin 3 → ℝ) => Fa κ b G₀ p.1 p.2 v) := by
  unfold Fa ghat
  have h1 : Measurable (fun p : (ℝ × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
      (((cb b * p.1.1 ^ (b / 2 - 1) : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_const.mul
      ((measurable_fst.comp measurable_fst).pow_const _))
  have h2 : Measurable (fun p : (ℝ × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
      timeFourier (fun t => G₀ t v) p.1.2) :=
    (timeFourier_continuous (hG v)).measurable.comp (measurable_snd.comp measurable_fst)
  have h3 : Continuous (fun p : (ℝ × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
      Tk κ p.1.1 (p.1.2 0) (p.1.2 1) p.2) :=
    (continuous_Tk_joint hκ).comp (by fun_prop : Continuous (fun p : (ℝ × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
      (p.1.1, p.1.2, p.2)))
  exact h1.mul (h2.mul h3.measurable)

/-- The mixture norm bounds the sup norm, hence the `L¹` norm on the (compact) support. -/
theorem lintegral_enorm_Fa_le {V : Type*} {θ b : ℝ} (hθ0 : 0 ≤ θ) {κ : (Fin 3 → ℝ) → ℂ}
    (hκ : Continuous κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (a : ℝ × (Fin 2 → ℝ)) (v : V) :
    ∫⁻ τ, ‖Fa κ b G₀ a τ v‖ₑ ≤ volume (tsupport κ) * mixedFourierNorm00 θ (Fa κ b G₀ a) := by
  have hsup : ∀ τ, ‖Fa κ b G₀ a τ v‖ₑ ≤ mixedFourierNorm00 θ (Fa κ b G₀ a) := by
    intro τ
    exact (WaveTurbulence.Regref.enorm_le_timeFourierNorm_at hθ0 (fun τ => Fa κ b G₀ a τ v) τ
      (continuous_Fa_tau hκ b G₀ a v).continuousAt).trans
      (timeFourierNorm_slice_le_mixedFourierNorm00 θ (Fa κ b G₀ a) v)
  have hsupp : Function.support (fun τ => ‖Fa κ b G₀ a τ v‖ₑ) ⊆ tsupport κ := by
    intro τ hτ
    by_contra h
    apply hτ
    have : κ τ = 0 := by by_contra hk; exact h (subset_tsupport _ hk)
    simp [Fa_eq_zero v this]
  rw [← setLIntegral_eq_of_support_subset hsupp]
  calc ∫⁻ τ in tsupport κ, ‖Fa κ b G₀ a τ v‖ₑ
      ≤ ∫⁻ τ in tsupport κ, mixedFourierNorm00 θ (Fa κ b G₀ a) := lintegral_mono hsup
    _ = _ := by rw [setLIntegral_const, mul_comm]


/-- **Stage two**: the parameter integral `H` and its Fourier norm. -/
theorem mixedNorm_H_le {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4)
    (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) {κ : (Fin 3 → ℝ) → ℂ} (hκc : HasCompactSupport κ)
    (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hG : ∀ v, Integrable (fun t => G₀ t v)) (hfin : mixedFourierNorm00 (1 - η) G₀ < ⊤) :
    mixedFourierNorm00 θ (fun τ v => ∫ a, Fa κ (1 - 3 * η) G₀ a τ v ∂μα) ≤
      ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
        mixedFourierNorm00 (1 - η) G₀ := by
  have hκ := hκs.continuous
  have hbound := lintegral_mixedNorm_Fa_le hη0 hη4 hθ0 hθη hκc hκs G₀ hG
  have hN : timeFourierNorm θ κ < ⊤ := timeFourierNorm_lt_top_of_smooth_compact θ hκc hκs
  have hfin2 : ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
      mixedFourierNorm00 (1 - η) G₀ < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN) hfin
  have hvol : volume (tsupport κ) < ⊤ := hκc.isCompact.measure_lt_top
  refine le_trans ?_ hbound
  refine SumintSigned.mixedFourierNorm00_integral_le (μ := μα) θ (Fa κ (1 - 3 * η) G₀)
    (measurable_Fa hκ _ G₀ hG) (fun v => ?_) (fun a v => integrable_Fa_tau hκc hκ _ G₀ a v)
  refine ⟨(measurable_Fa hκ _ G₀ hG v).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [μα, lintegral_prod _ (measurable_Fa hκ _ G₀ hG v).enorm.aemeasurable]
  have hae : ∀ᵐ a ∂μα, ∫⁻ τ, ‖Fa κ (1 - 3 * η) G₀ a τ v‖ₑ ≤
      volume (tsupport κ) * mixedFourierNorm00 θ (Fa κ (1 - 3 * η) G₀ a) :=
    Filter.Eventually.of_forall fun a => lintegral_enorm_Fa_le hθ0 hκ G₀ a v
  calc _ ≤ ∫⁻ a, volume (tsupport κ) * mixedFourierNorm00 θ (Fa κ (1 - 3 * η) G₀ a) ∂μα :=
        lintegral_mono_ae hae
    _ = volume (tsupport κ) * ∫⁻ a, mixedFourierNorm00 θ (Fa κ (1 - 3 * η) G₀ a) ∂μα :=
        lintegral_const_mul' _ _ hvol.ne
    _ < ⊤ := ENNReal.mul_lt_top hvol (lt_of_le_of_lt hbound hfin2)


/-- The Gamma integral: `∫₀^∞ c_b s^{b/2-1} e^{-s u²} ds = |u|^{-b}`. -/
theorem integral_gamma_mixture {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : u ≠ 0) :
    ∫ s in Ioi (0 : ℝ), cb b * s ^ (b / 2 - 1) * Real.exp (-(s * u ^ 2)) = |u| ^ (-b) := by
  have hu2 : 0 < u ^ 2 := by positivity
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := b / 2) (r := u ^ 2) (by linarith) hu2
  have e : ∀ s : ℝ, cb b * s ^ (b / 2 - 1) * Real.exp (-(s * u ^ 2)) =
      cb b * (s ^ (b / 2 - 1) * Real.exp (-(u ^ 2 * s))) := by
    intro s; rw [mul_comm s]; ring
  simp_rw [e]
  rw [integral_const_mul, h]
  unfold cb
  have hG : 0 < Real.Gamma (b / 2) := Real.Gamma_pos_of_pos (by linarith)
  have e2 : (1 / u ^ 2) ^ (b / 2) = |u| ^ (-b) := by
    have h1 : 1 / u ^ 2 = |u| ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (abs_nonneg u), Real.rpow_two, sq_abs, one_div]
    rw [h1, ← Real.rpow_mul (abs_nonneg u)]
    congr 1; ring
  rw [e2]
  field_simp

theorem integrable_gamma_mixture {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : u ≠ 0) :
    IntegrableOn (fun s : ℝ => cb b * s ^ (b / 2 - 1) * Real.exp (-(s * u ^ 2))) (Ioi 0) := by
  have hu2 : 0 < u ^ 2 := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b / 2 - 1) (b := u ^ 2)
    (by linarith) one_pos hu2
  refine IntegrableOn.congr_fun (f := fun x => cb b * (x ^ (b / 2 - 1) * Real.exp (-u ^ 2 * x ^ 1)))
    (h.const_mul (cb b))
    (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [neg_mul, mul_comm (u ^ 2) s]; ring_nf


theorem timeFourier_neg_eval {r : ℕ} (f : (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) :
    timeFourier f (-t) = ∫ l, ((Real.fourierChar (timePairing r l t) : Circle) : ℂ) * f l := by
  unfold timeFourier VectorFourier.fourierIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only [map_neg, neg_neg, Circle.smul_def, smul_eq_mul]

theorem timePairing2 (l t : Fin 2 → ℝ) :
    timePairing 2 l t = l 0 * t 0 + l 1 * t 1 := by
  simp [timePairing, dotProduct, Fin.sum_univ_two]

theorem inversion_ee {g : (Fin 2 → ℝ) → ℂ} (hg : Integrable g) (hhat : Integrable (timeFourier g)) :
    ∀ᵐ t : Fin 2 → ℝ, ∫ l, ee (l 0 * t 0 + l 1 * t 1) * timeFourier g l = g t := by
  filter_upwards [Regref.timeFourier_inversion_ae hg hhat] with t ht
  rw [← ht, timeFourier_neg_eval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only [timePairing2, ee_eq_fourierChar]

theorem integrable_ee_mul {ĝ : (Fin 2 → ℝ) → ℂ} (h : Integrable ĝ) (a c : ℝ) :
    Integrable (fun l : Fin 2 → ℝ => ee (l 0 * a + l 1 * c) * ĝ l) := by
  refine h.norm.mono' ?_ ?_
  · exact ((continuous_ee.comp (by fun_prop)).aestronglyMeasurable).mul h.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun l => by rw [norm_mul, norm_ee, one_mul]


theorem Fa_factor {V : Type*} (κ : (Fin 3 → ℝ) → ℂ) (b : ℝ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (s : ℝ) (l : Fin 2 → ℝ) (τ : Fin 3 → ℝ) (v : V) :
    Fa κ b G₀ (s, l) τ v =
      (((cb b * s ^ (b / 2 - 1) * Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ)) : ℂ) *
        (κ τ * (ee (l 0 * τ 0 + l 1 * τ 2) * ghat G₀ l v -
          ee (l 0 * τ 1 + l 1 * τ 2) * ghat G₀ l v)) := by
  simp only [Fa, Tk]
  rw [show l 0 * τ 0 + l 1 * τ 2 = l 0 * τ 0 + l 1 * τ 2 from rfl, ee_add, ee_add]
  push_cast
  ring

/-- **The identification of the parameter integral.** -/
theorem integral_Fa_eq {V : Type*} (κ : (Fin 3 → ℝ) → ℂ) {b : ℝ} (hb : 0 < b)
    (G₀ : (Fin 2 → ℝ) → V → ℂ) (v : V) (τ : Fin 3 → ℝ) (hu : τ 0 ≠ τ 1)
    (hhat : Integrable (timeFourier (fun t => G₀ t v)))
    (h0 : ∫ l, ee (l 0 * τ 0 + l 1 * τ 2) * ghat G₀ l v = G₀ ![τ 0, τ 2] v)
    (h1 : ∫ l, ee (l 0 * τ 1 + l 1 * τ 2) * ghat G₀ l v = G₀ ![τ 1, τ 2] v) :
    ∫ a, Fa κ b G₀ a τ v ∂μα =
      κ τ * ((|τ 0 - τ 1| ^ (-b) : ℝ) : ℂ) * (G₀ ![τ 0, τ 2] v - G₀ ![τ 1, τ 2] v) := by
  have hu' : τ 0 - τ 1 ≠ 0 := sub_ne_zero.mpr hu
  set φ : ℝ → ℂ := fun s => (((cb b * s ^ (b / 2 - 1) * Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ)) : ℂ)
    with hφ
  set Ψ : (Fin 2 → ℝ) → ℂ := fun l => κ τ * (ee (l 0 * τ 0 + l 1 * τ 2) * ghat G₀ l v -
    ee (l 0 * τ 1 + l 1 * τ 2) * ghat G₀ l v) with hΨ
  have hF : ∀ p : ℝ × (Fin 2 → ℝ), Fa κ b G₀ p τ v = φ p.1 * Ψ p.2 := fun p => Fa_factor κ b G₀ p.1 p.2 τ v
  have hφi : Integrable φ (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_gamma_mixture hb hu').ofReal
  have hgh : Integrable (fun l => ghat G₀ l v) := hhat
  have hΨi : Integrable Ψ :=
    ((integrable_ee_mul hgh (τ 0) (τ 2)).sub (integrable_ee_mul hgh (τ 1) (τ 2))).const_mul (κ τ)
  have hφint : ∫ s, φ s ∂(volume.restrict (Ioi (0 : ℝ))) = ((|τ 0 - τ 1| ^ (-b) : ℝ) : ℂ) := by
    rw [hφ, integral_complex_ofReal]
    congr 1
    exact integral_gamma_mixture hb hu'
  have hΨint : ∫ l, Ψ l = κ τ * (G₀ ![τ 0, τ 2] v - G₀ ![τ 1, τ 2] v) := by
    rw [hΨ, integral_const_mul, integral_sub (integrable_ee_mul hgh (τ 0) (τ 2))
      (integrable_ee_mul hgh (τ 1) (τ 2)), h0, h1]
  simp_rw [hF]
  unfold μα
  rw [integral_prod_mul, hφint, hΨint]
  ring


theorem ae_pull_succAbove (i : Fin 3) {P : (Fin 2 → ℝ) → Prop} (h : ∀ᵐ t : Fin 2 → ℝ, P t) :
    ∀ᵐ τ : Fin 3 → ℝ, P (fun j => τ (i.succAbove j)) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hq : QuasiMeasurePreserving
      (fun τ : Fin 3 → ℝ => fun j : Fin 2 => τ (i.succAbove j)) volume volume := by
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Fin 2 → ℝ)))).comp hmp.quasiMeasurePreserving
    exact h2
  exact hq.ae h

theorem ae_pull02 {P : (Fin 2 → ℝ) → Prop} (h : ∀ᵐ t : Fin 2 → ℝ, P t) :
    ∀ᵐ τ : Fin 3 → ℝ, P ![τ 0, τ 2] := by
  filter_upwards [ae_pull_succAbove 1 h] with τ hτ
  have : (fun j : Fin 2 => τ ((1 : Fin 3).succAbove j)) = ![τ 0, τ 2] := by
    funext j; fin_cases j <;> rfl
  rwa [this] at hτ

theorem ae_pull12 {P : (Fin 2 → ℝ) → Prop} (h : ∀ᵐ t : Fin 2 → ℝ, P t) :
    ∀ᵐ τ : Fin 3 → ℝ, P ![τ 1, τ 2] := by
  filter_upwards [ae_pull_succAbove 0 h] with τ hτ
  have : (fun j : Fin 2 => τ ((0 : Fin 3).succAbove j)) = ![τ 1, τ 2] := by
    funext j; fin_cases j <;> rfl
  rwa [this] at hτ

theorem ae_ne_01 : ∀ᵐ τ : Fin 3 → ℝ, τ 0 ≠ τ 1 := by
  have hker : (volume : Measure (Fin 3 → ℝ)) {τ | τ 0 = τ 1} = 0 := by
    let f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1
    have hne : LinearMap.ker f ≠ ⊤ := by
      intro h
      have : (Pi.single 0 1 : Fin 3 → ℝ) ∈ LinearMap.ker f := by rw [h]; trivial
      simp [f] at this
    have := Measure.addHaar_submodule (volume : Measure (Fin 3 → ℝ)) _ hne
    convert this using 2
    ext τ
    simp [f, sub_eq_zero]
  rw [ae_iff]
  simpa using hker


/-- **F2, almost-everywhere form** (TARGET `vineest` Step 4, clause (c); L1903).
For `G₀ ∈ 𝔛^{1-η}(ℝ²)` and a smooth compactly supported cutoff `κ` on `ℝ³` there is `H` on `ℝ³`
(the divided difference in the first coordinate) with `‖H‖_{𝔛^θ} ≲ ‖κ‖_{𝔛^θ} ‖G₀‖_{𝔛^{1-η}}`
and `H(τ) = κ(τ) |τ₀-τ₁|^{-(1-3η)} (G₀(τ₀,τ₂) - G₀(τ₁,τ₂))` for a.e. `τ`. -/
theorem timeDiff_extraction_ae {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η)
    (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) {κ : (Fin 3 → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hfin : mixedFourierNorm00 (1 - η) G₀ < ⊤) :
    ∃ H : (Fin 3 → ℝ) → V → ℂ,
      mixedFourierNorm00 θ H ≤ ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
        mixedFourierNorm00 (1 - η) G₀ ∧
      ∀ᵐ τ : Fin 3 → ℝ, ∀ v, H τ v =
        κ τ * ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
          (G₀ ![τ 0, τ 2] v - G₀ ![τ 1, τ 2] v) := by
  have hb : 0 < 1 - 3 * η := by linarith
  have hG : ∀ v, Integrable (fun t => G₀ t v) := fun v => integrable_of_mixedFourierNorm00_lt_top hfin v
  refine ⟨fun τ v => ∫ a, Fa κ (1 - 3 * η) G₀ a τ v ∂μα,
    mixedNorm_H_le hη0 hη4 hθ0 hθη hκc hκs G₀ hG hfin, ?_⟩
  rw [ae_all_iff]
  intro v
  have hhat : Integrable (timeFourier (fun t => G₀ t v)) :=
    integrable_timeFourier_of_norm_lt_top (by linarith) ((timeFourierNorm_slice_le_mixedFourierNorm00
      (1 - η) G₀ v).trans_lt hfin)
  have hinv := inversion_ee (hG v) hhat
  filter_upwards [ae_pull02 hinv, ae_pull12 hinv, ae_ne_01] with τ h0 h1 hne
  exact integral_Fa_eq κ hb G₀ v τ hne hhat (by simpa [ghat] using h0) (by simpa [ghat] using h1)

end WaveTurbulence.VineEstS4c.TimeDiff

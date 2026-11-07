/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffKernel
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffScalar
public import WaveTurbulence.Foundations.Regref.FourierAE
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (c): stage-two norm bound

The mixture `Fa (s, λ)(τ, v) = c_b s^{b/2-1} ĝ(λ, v) Tk κ s λ₀ λ₁ τ` and the bound
`∫⁻ 𝔛^θ(Fa a) da ≲ ‖κ‖_{𝔛^θ} ‖G₀‖_{𝔛^{1-η}}`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Real Complex Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.VineEstS4c.TimeDiff

open WaveTurbulence.Fourier

/-- The Gamma-mixture constant `1/Γ(b/2)`. -/
@[expose] noncomputable def cb (b : ℝ) : ℝ := 1 / Real.Gamma (b / 2)

theorem cb_pos {b : ℝ} (hb : 0 < b) : 0 < cb b := by
  unfold cb; have := Real.Gamma_pos_of_pos (by linarith : 0 < b / 2); positivity

/-- The time Fourier coefficients of the slices of `G₀`. -/
@[expose] noncomputable def ghat {V : Type*} (G₀ : (Fin 2 → ℝ) → V → ℂ) (l : Fin 2 → ℝ) (v : V) : ℂ :=
  timeFourier (fun t => G₀ t v) l

/-- The mixture family. -/
@[expose] noncomputable def Fa {V : Type*} (κ : (Fin 3 → ℝ) → ℂ) (b : ℝ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (a : ℝ × (Fin 2 → ℝ)) (τ : Fin 3 → ℝ) (v : V) : ℂ :=
  ((cb b * a.1 ^ (b / 2 - 1) : ℝ) : ℂ) * (ghat G₀ a.2 v * Tk κ a.1 (a.2 0) (a.2 1) τ)

/-- The parameter measure. -/
@[expose] noncomputable def μα : Measure (ℝ × (Fin 2 → ℝ)) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Fin 2 → ℝ))

/-- Output supremum factors through a scalar-times-profile product. -/
theorem mixedFourierNorm00_mul_profile {V : Type*} (θ : ℝ) (g : V → ℂ) {T : (Fin 3 → ℝ) → ℂ}
    (hT : Integrable T) :
    mixedFourierNorm00 θ (fun τ v => g v * T τ) =
      (⨆ v, ‖g v‖ₑ) * timeFourierNorm θ T := by
  have hi : ∀ v, Integrable (fun τ => g v * T τ) := fun v => hT.const_mul _
  rw [mixedFourierNorm00_eq_lintegral hi, timeFourierNorm_eq_lintegral hT]
  have he : ∀ ξ, mixedFourierEnvelope00 (fun τ v => g v * T τ) ξ =
      (⨆ v, ‖g v‖ₑ) * ‖timeFourier T ξ‖ₑ := by
    intro ξ
    unfold mixedFourierEnvelope00
    simp_rw [show ∀ v, timeFourier (fun τ => g v * T τ) ξ = g v * timeFourier T ξ from
      fun v => congrFun (timeFourier_smul (g v) T) ξ, enorm_mul]
    exact (ENNReal.iSup_mul _ _).symm
  simp_rw [he]
  rw [← lintegral_const_mul]
  · congr 1; funext ξ; ring
  · exact (timeWeight_measurable θ).mul ((timeFourier_continuous hT).measurable.enorm)


theorem norm_Tk_le (κ : (Fin 3 → ℝ) → ℂ) {s : ℝ} (hs : 0 ≤ s) (μ l : ℝ) (τ : Fin 3 → ℝ) :
    ‖Tk κ s μ l τ‖ ≤ 2 * ‖κ τ‖ := by
  unfold Tk
  have h1 : ‖((Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hs (sq_nonneg (τ 0 - τ 1))]
  have h2 : ‖ee (μ * τ 0) - ee (μ * τ 1)‖ ≤ 2 := by
    calc _ ≤ ‖ee (μ * τ 0)‖ + ‖ee (μ * τ 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_ee, norm_ee]; norm_num
  rw [norm_mul, norm_mul, norm_mul, norm_ee, mul_one]
  have hk := norm_nonneg (κ τ)
  have h3 := norm_nonneg (ee (μ * τ 0) - ee (μ * τ 1))
  have h4 := norm_nonneg (((Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ) : ℂ))
  calc ‖κ τ‖ * ‖((Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ) : ℂ)‖ * ‖ee (μ * τ 0) - ee (μ * τ 1)‖
      ≤ ‖κ τ‖ * 1 * 2 := by gcongr
    _ = _ := by ring

theorem continuous_Tk {κ : (Fin 3 → ℝ) → ℂ} (hκ : Continuous κ) (s μ l : ℝ) :
    Continuous (Tk κ s μ l) := by
  unfold Tk
  have : Continuous (fun τ : Fin 3 → ℝ => ((Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ) : ℂ)) := by
    fun_prop
  exact ((hκ.mul this).mul ((continuous_ee.comp (continuous_const.mul (by fun_prop))).sub
    (continuous_ee.comp (continuous_const.mul (by fun_prop))))).mul
    (continuous_ee.comp (continuous_const.mul (by fun_prop)))

theorem integrable_Tk {κ : (Fin 3 → ℝ) → ℂ} (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ)
    {s : ℝ} (hs : 0 ≤ s) (μ l : ℝ) : Integrable (Tk κ s μ l) := by
  have hκi : Integrable κ := hκs.continuous.integrable_of_hasCompactSupport hκc
  refine (hκi.norm.const_mul 2).mono' (continuous_Tk hκs.continuous s μ l).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun τ => norm_Tk_le κ hs μ l τ

/-- The profile-level bound for one mixture component. -/
theorem mixedNorm_Fa_le {V : Type*} {θ b : ℝ} (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {κ : (Fin 3 → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    {a : ℝ × (Fin 2 → ℝ)} (ha : 0 < a.1) :
    mixedFourierNorm00 θ (Fa κ b G₀ a) ≤
      ENNReal.ofReal (cb b * a.1 ^ (b / 2 - 1)) * (⨆ v, ‖ghat G₀ a.2 v‖ₑ) *
        (ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (a.2 0) (a.2 1) ^ θ *
          kerFac θ (a.2 0) a.1) * timeFourierNorm θ κ) := by
  have hT := integrable_Tk hκc hκs ha.le (a.2 0) (a.2 1)
  have h1 : Fa κ b G₀ a = fun τ v => ((cb b * a.1 ^ (b / 2 - 1) : ℝ) : ℂ) •
      (fun τ v => ghat G₀ a.2 v * Tk κ a.1 (a.2 0) (a.2 1) τ) τ v := by
    funext τ v; simp only [Fa, smul_eq_mul]
  rw [h1, SumintSigned.mixedFourierNorm00_smul, mixedFourierNorm00_mul_profile θ _ hT]
  have h2 : ‖((cb b * a.1 ^ (b / 2 - 1) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (cb b * a.1 ^ (b / 2 - 1)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (cb_pos hb).le (Real.rpow_nonneg ha.le _))]
  rw [h2, mul_assoc]
  gcongr
  have := mixedNorm_Tk_le hθ0 hθ1 hκc hκs ha (a.2 0) (a.2 1)
  rwa [mixedFourierNorm00_unit] at this


/-- The total constant of the stage-two bound. -/
@[expose] noncomputable def CtotB (b θ : ℝ) : ℝ :=
  cb b * (4 ^ θ * (2 * π ^ 2 * Mg)) *
    (4 ^ (θ / 2) * (2 / b + 2 / (b - θ) + 2 / (1 - b - θ)))

theorem CtotB_nonneg {b θ : ℝ} (hb : 0 < b) (hθb : θ < b) (hbθ : b + θ < 1) : 0 ≤ CtotB b θ := by
  unfold CtotB
  have h1 := cb_pos hb
  have h2 : 0 < 2 / (b - θ) := div_pos two_pos (by linarith)
  have h3 : 0 < 2 / (1 - b - θ) := div_pos two_pos (by linarith)
  have h4 : 0 < 2 / b := div_pos two_pos hb
  have := Mg_nonneg
  positivity

theorem measurable_Bd {V : Type*} [Countable V] {θ b : ℝ} (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hG : ∀ v, Integrable (fun t => G₀ t v)) (N : ℝ≥0∞) :
    Measurable (fun a : ℝ × (Fin 2 → ℝ) =>
      ENNReal.ofReal (cb b * a.1 ^ (b / 2 - 1)) * (⨆ v, ‖ghat G₀ a.2 v‖ₑ) *
        (ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (a.2 0) (a.2 1) ^ θ *
          kerFac θ (a.2 0) a.1) * N)) := by
  have hE : Measurable (fun l : Fin 2 → ℝ => ⨆ v, ‖ghat G₀ l v‖ₑ) :=
    measurable_mixedFourierEnvelope00 hG
  have h1 : Measurable (fun a : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal (cb b * a.1 ^ (b / 2 - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const _))
  have h2 : Measurable (fun a : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) *
      Bw (a.2 0) (a.2 1) ^ θ * kerFac θ (a.2 0) a.1)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold Bw kerFac
    have hm0 : Measurable (fun a : ℝ × (Fin 2 → ℝ) => a.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    have hm1 : Measurable (fun a : ℝ × (Fin 2 → ℝ) => a.2 1) :=
      (measurable_pi_apply 1).comp measurable_snd
    have hs : Measurable (fun a : ℝ × (Fin 2 → ℝ) => a.1) := measurable_fst
    fun_prop
  exact (h1.mul (hE.comp measurable_snd)).mul (h2.mul measurable_const)


theorem bracket_bound {θ b : ℝ} (hθ0 : 0 ≤ θ) (hb : 0 < b) (l : Fin 2 → ℝ) :
    Bw (l 0) (l 1) ^ θ * (1 + l 0 ^ 2) ^ ((b + θ) / 2) ≤
      (WaveTurbulence.Fourier.timeBracket l) ^ (b + 2 * θ) := by
  have h0 : √(1 + l 0 ^ 2) ≤ timeBracket l := bracket_le_timeBracket l 0
  have h1 : √(1 + l 1 ^ 2) ≤ timeBracket l := bracket_le_timeBracket l 1
  have hBw : Bw (l 0) (l 1) ≤ timeBracket l := max_le h0 h1
  have hB0 : 0 ≤ Bw (l 0) (l 1) := by linarith [one_le_Bw (l 0) (l 1)]
  have hT := one_le_timeBracket l
  have e1 : (1 + l 0 ^ 2) ^ ((b + θ) / 2) = (√(1 + l 0 ^ 2)) ^ (b + θ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have e2 : (timeBracket l) ^ (b + 2 * θ) = timeBracket l ^ θ * timeBracket l ^ (b + θ) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [e1, e2]
  have := Real.rpow_le_rpow hB0 hBw hθ0
  have h3 := Real.rpow_le_rpow (Real.sqrt_nonneg _) h0 (by linarith : 0 ≤ b + θ)
  exact mul_le_mul this h3 (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (by linarith) _)

theorem inner_s_bound {θ b : ℝ} (hθ0 : 0 ≤ θ) (hθb : θ < b) (hbθ : b + θ < 1) (hb : 0 < b)
    (l : Fin 2 → ℝ) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (cb b * s ^ (b / 2 - 1)) *
        ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ * kerFac θ (l 0) s) ≤
      ENNReal.ofReal (CtotB b θ * (WaveTurbulence.Fourier.timeBracket l) ^ (b + 2 * θ)) := by
  have hB0 : 0 ≤ Bw (l 0) (l 1) ^ θ := Real.rpow_nonneg (by linarith [one_le_Bw (l 0) (l 1)]) _
  have hMg := Mg_nonneg
  have hcb := cb_pos hb
  have hCk : 0 ≤ 4 ^ θ * (2 * π ^ 2 * Mg) := by positivity
  have h1 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (cb b * s ^ (b / 2 - 1)) *
        ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ * kerFac θ (l 0) s) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (cb b * (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ)) *
        ENNReal.ofReal (scaleInt b θ (l 0) s) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have hk : 0 ≤ kerFac θ (l 0) s := by
      unfold kerFac
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_min zero_le_one (by positivity))
    rw [← ENNReal.ofReal_mul (mul_nonneg hcb.le (Real.rpow_nonneg hs'.le _)),
      ← ENNReal.ofReal_mul (mul_nonneg hcb.le (mul_nonneg hCk hB0))]
    congr 1
    unfold scaleInt kerFac
    ring
  rw [h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right (lintegral_scaleInt_le hθ0 hθb hbθ (l 0)) _).trans ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg hcb.le (mul_nonneg hCk hB0))]
  apply ENNReal.ofReal_le_ofReal
  have hbr := bracket_bound (θ := θ) (b := b) hθ0 hb l
  have hC : 0 ≤ cb b * (4 ^ θ * (2 * π ^ 2 * Mg)) *
      (4 ^ (θ / 2) * (2 / b + 2 / (b - θ) + 2 / (1 - b - θ))) := CtotB_nonneg hb hθb hbθ
  have e : cb b * (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ) *
      (4 ^ (θ / 2) * (2 / b + 2 / (b - θ) + 2 / (1 - b - θ)) * (1 + l 0 ^ 2) ^ ((b + θ) / 2)) =
      (cb b * (4 ^ θ * (2 * π ^ 2 * Mg)) *
        (4 ^ (θ / 2) * (2 / b + 2 / (b - θ) + 2 / (1 - b - θ)))) *
        (Bw (l 0) (l 1) ^ θ * (1 + l 0 ^ 2) ^ ((b + θ) / 2)) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hbr hC


/-- **Stage two, norm bound**: the integral of the mixture norms. -/
theorem lintegral_mixedNorm_Fa_le {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η)
    (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) {κ : (Fin 3 → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hG : ∀ v, Integrable (fun t => G₀ t v)) :
    ∫⁻ a, mixedFourierNorm00 θ (Fa κ (1 - 3 * η) G₀ a) ∂μα ≤
      ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
        mixedFourierNorm00 (1 - η) G₀ := by
  set b := 1 - 3 * η with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  have hθb : θ < b := by rw [hbdef]; linarith
  have hbθ : b + θ < 1 := by rw [hbdef]; linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hexp : b + 2 * θ ≤ 1 - η := by rw [hbdef]; linarith
  set N := timeFourierNorm θ κ with hN
  have hae : ∀ᵐ a ∂μα, 0 < a.1 := by
    have h1 : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 < s :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => hs)
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hmeas := measurable_Bd (θ := θ) (b := b) G₀ hG N
  calc ∫⁻ a, mixedFourierNorm00 θ (Fa κ b G₀ a) ∂μα
      ≤ ∫⁻ a, ENNReal.ofReal (cb b * a.1 ^ (b / 2 - 1)) * (⨆ v, ‖ghat G₀ a.2 v‖ₑ) *
        (ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (a.2 0) (a.2 1) ^ θ *
          kerFac θ (a.2 0) a.1) * N) ∂μα := by
        apply lintegral_mono_ae
        filter_upwards [hae] with a ha
        exact mixedNorm_Fa_le hb hθ0 hθ1 hκc hκs G₀ ha
    _ = ∫⁻ l, ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (cb b * s ^ (b / 2 - 1)) * (⨆ v, ‖ghat G₀ l v‖ₑ) *
        (ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ *
          kerFac θ (l 0) s) * N) := by
        unfold μα
        exact lintegral_prod_symm _ hmeas.aemeasurable
    _ ≤ ∫⁻ l, (⨆ v, ‖ghat G₀ l v‖ₑ) * N * (ENNReal.ofReal (CtotB b θ) *
          ENNReal.ofReal ((timeBracket l) ^ (1 - η))) := by
        apply lintegral_mono
        intro l
        have hi : ∀ s, ENNReal.ofReal (cb b * s ^ (b / 2 - 1)) * (⨆ v, ‖ghat G₀ l v‖ₑ) *
            (ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ * kerFac θ (l 0) s) * N) =
            ((⨆ v, ‖ghat G₀ l v‖ₑ) * N) * (ENNReal.ofReal (cb b * s ^ (b / 2 - 1)) *
              ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ * kerFac θ (l 0) s)) := by
          intro s; ring
        simp_rw [hi]
        rw [lintegral_const_mul]
        · refine mul_le_mul_right ((inner_s_bound hθ0 hθb hbθ hb l).trans ?_) _
          rw [← ENNReal.ofReal_mul (CtotB_nonneg hb hθb hbθ)]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (CtotB_nonneg hb hθb hbθ)
          exact Real.rpow_le_rpow_of_exponent_le (one_le_timeBracket l) hexp
        · have hm : Measurable (fun s : ℝ => ENNReal.ofReal (cb b * s ^ (b / 2 - 1)) *
              ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw (l 0) (l 1) ^ θ * kerFac θ (l 0) s)) := by
            unfold Bw kerFac
            fun_prop
          exact hm
    _ = ENNReal.ofReal (CtotB b θ) * N * mixedFourierNorm00 (1 - η) G₀ := by
        rw [mixedFourierNorm00_eq_lintegral hG]
        simp_rw [show ∀ ξ : Fin 2 → ℝ, (⨆ v, ‖ghat G₀ ξ v‖ₑ) * N *
          (ENNReal.ofReal (CtotB b θ) * ENNReal.ofReal ((timeBracket ξ) ^ (1 - η))) =
          (ENNReal.ofReal (CtotB b θ) * N) * (timeWeight (1 - η) ξ * mixedFourierEnvelope00 G₀ ξ) from
          fun ξ => by unfold timeWeight mixedFourierEnvelope00 ghat; ring]
        rw [lintegral_const_mul]
        exact (timeWeight_measurable _).mul (measurable_mixedFourierEnvelope00 hG)

end WaveTurbulence.VineEstS4c.TimeDiff

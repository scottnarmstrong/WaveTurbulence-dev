/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffRestr
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceBound
import Mathlib.Tactic

/-! # W2-KIND2 Lemma B: the time-difference extraction from an `𝔛^{1-2η}` input (R114, TARGET L1918-L1920)

The versions of `lintegral_mixedNorm_Fa_le`, `mixedNorm_H_le`, `timeDiff_extraction_ae`, `timeDiff_extraction` of `VineEstS4c.TimeDiff`
with the input norm `𝔛^{1-2η}` instead of `𝔛^{1-η}`, keeping the extracted factor `|τ₀ - τ₁|^{-(1-3η)}`.  The only change in the proofs is the
exponent comparison `b + 2θ ≤ 1 - 2η` (with `b = 1 - 3η`), i.e. the output regularity must satisfy `2 θ ≤ η` (the code uses `θ = 6 η⁶`, see
`two_theta_le`).  Statements are the originals with `(1 - η) → (1 - 2 * η)` and `θ ≤ η → 2 * θ ≤ η`.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Real Complex Set
open scoped ENNReal ContDiff
open Classical

namespace WaveTurbulence.VineEstS4c.TimeDiff

open WaveTurbulence.Fourier

/-- **Stage two, norm bound**: the integral of the mixture norms. -/
theorem lintegral_mixedNorm_Fa_le2 {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η)
    (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : 2 * θ ≤ η) {κ : (Fin 3 → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hG : ∀ v, Integrable (fun t => G₀ t v)) :
    ∫⁻ a, mixedFourierNorm00 θ (Fa κ (1 - 3 * η) G₀ a) ∂μα ≤
      ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
        mixedFourierNorm00 (1 - 2 * η) G₀ := by
  set b := 1 - 3 * η with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  have hθb : θ < b := by rw [hbdef]; linarith
  have hbθ : b + θ < 1 := by rw [hbdef]; linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hexp : b + 2 * θ ≤ 1 - 2 * η := by rw [hbdef]; linarith
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
          ENNReal.ofReal ((timeBracket l) ^ (1 - 2 * η))) := by
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
    _ = ENNReal.ofReal (CtotB b θ) * N * mixedFourierNorm00 (1 - 2 * η) G₀ := by
        rw [mixedFourierNorm00_eq_lintegral hG]
        simp_rw [show ∀ ξ : Fin 2 → ℝ, (⨆ v, ‖ghat G₀ ξ v‖ₑ) * N *
          (ENNReal.ofReal (CtotB b θ) * ENNReal.ofReal ((timeBracket ξ) ^ (1 - 2 * η))) =
          (ENNReal.ofReal (CtotB b θ) * N) * (timeWeight (1 - 2 * η) ξ * mixedFourierEnvelope00 G₀ ξ) from
          fun ξ => by unfold timeWeight mixedFourierEnvelope00 ghat; ring]
        rw [lintegral_const_mul]
        exact (timeWeight_measurable _).mul (measurable_mixedFourierEnvelope00 hG)


/-- **Stage two**: the parameter integral `H` and its Fourier norm. -/
theorem mixedNorm_H_le2 {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4)
    (hθ0 : 0 ≤ θ) (hθη : 2 * θ ≤ η) {κ : (Fin 3 → ℝ) → ℂ} (hκc : HasCompactSupport κ)
    (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hG : ∀ v, Integrable (fun t => G₀ t v)) (hfin : mixedFourierNorm00 (1 - 2 * η) G₀ < ⊤) :
    mixedFourierNorm00 θ (fun τ v => ∫ a, Fa κ (1 - 3 * η) G₀ a τ v ∂μα) ≤
      ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
        mixedFourierNorm00 (1 - 2 * η) G₀ := by
  have hκ := hκs.continuous
  have hbound := lintegral_mixedNorm_Fa_le2 hη0 hη4 hθ0 hθη hκc hκs G₀ hG
  have hN : timeFourierNorm θ κ < ⊤ := timeFourierNorm_lt_top_of_smooth_compact θ hκc hκs
  have hfin2 : ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
      mixedFourierNorm00 (1 - 2 * η) G₀ < ⊤ :=
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



/-- **F2, almost-everywhere form** (TARGET `vineest` Step 4, clause (c); L1903).
For `G₀ ∈ 𝔛^{1-η}(ℝ²)` and a smooth compactly supported cutoff `κ` on `ℝ³` there is `H` on `ℝ³`
(the divided difference in the first coordinate) with `‖H‖_{𝔛^θ} ≲ ‖κ‖_{𝔛^θ} ‖G₀‖_{𝔛^{1-η}}`
and `H(τ) = κ(τ) |τ₀-τ₁|^{-(1-3η)} (G₀(τ₀,τ₂) - G₀(τ₁,τ₂))` for a.e. `τ`. -/
theorem timeDiff_extraction_ae2 {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η)
    (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : 2 * θ ≤ η) {κ : (Fin 3 → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) (G₀ : (Fin 2 → ℝ) → V → ℂ)
    (hfin : mixedFourierNorm00 (1 - 2 * η) G₀ < ⊤) :
    ∃ H : (Fin 3 → ℝ) → V → ℂ,
      mixedFourierNorm00 θ H ≤ ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ *
        mixedFourierNorm00 (1 - 2 * η) G₀ ∧
      ∀ᵐ τ : Fin 3 → ℝ, ∀ v, H τ v =
        κ τ * ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
          (G₀ ![τ 0, τ 2] v - G₀ ![τ 1, τ 2] v) := by
  have hb : 0 < 1 - 3 * η := by linarith
  have hG : ∀ v, Integrable (fun t => G₀ t v) := fun v => integrable_of_mixedFourierNorm00_lt_top hfin v
  refine ⟨fun τ v => ∫ a, Fa κ (1 - 3 * η) G₀ a τ v ∂μα,
    mixedNorm_H_le2 hη0 hη4 hθ0 hθη hκc hκs G₀ hG hfin, ?_⟩
  rw [ae_all_iff]
  intro v
  have hhat : Integrable (timeFourier (fun t => G₀ t v)) :=
    integrable_timeFourier_of_norm_lt_top (by linarith) ((timeFourierNorm_slice_le_mixedFourierNorm00
      (1 - 2 * η) G₀ v).trans_lt hfin)
  have hinv := inversion_ee (hG v) hhat
  filter_upwards [ae_pull02 hinv, ae_pull12 hinv, ae_ne_01] with τ h0 h1 hne
  exact integral_Fa_eq κ hb G₀ v τ hne hhat (by simpa [ghat] using h0) (by simpa [ghat] using h1)


/-- **F2** (TARGET `vineest` Step 4, clause (c); L1903): the divided time difference of an
`𝔛^{1-η}` function, with the factor `|τ₀-τ₁|^{-(1-3η)}`, is an `𝔛^θ` function (`θ ≤ η`). -/
theorem timeDiff_extraction2 {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4)
    (hθ0 : 0 ≤ θ) (hθη : 2 * θ ≤ η) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (F : (Fin 2 → ℝ) → V → ℂ) (B2 : Set (Fin 2 → ℝ))
      (B3 : Set (Fin 3 → ℝ)) (K : Set V),
      (∀ τ ∈ B3, ‖τ‖ ≤ R) → (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr θ B3 K (fun τ v => ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
          (F ![τ 0, τ 2] v - F ![τ 1, τ 2] v)) ≤ C * XNorm00Restr (1 - 2 * η) B2 K F := by
  obtain ⟨κ, hκc, hκs, hκ1⟩ := exists_cutoff R
  have hN : timeFourierNorm θ κ < ⊤ := timeFourierNorm_lt_top_of_smooth_compact θ hκc hκs
  refine ⟨ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ + 1,
    ENNReal.add_ne_top.mpr ⟨(ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN).ne, ENNReal.one_ne_top⟩,
    ?_⟩
  intro F B2 B3 K hR hB
  set C : ℝ≥0∞ := ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ + 1 with hC
  have hC0 : C ≠ 0 := by rw [hC]; exact (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self))
  have hCt : C ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨(ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN).ne, ENNReal.one_ne_top⟩
  unfold XNorm00Restr
  rw [ENNReal.mul_iInf_of_ne hC0 hCt]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hC0 hCt]
  refine le_iInf fun hG => ?_
  by_cases htop : XNorm00 (1 - 2 * η) G = ⊤
  · rw [htop, ENNReal.mul_top hC0]; exact le_top
  have hfin : mixedFourierNorm00 (1 - 2 * η) G < ⊤ := by
    rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact lt_top_iff_ne_top.mpr htop
  obtain ⟨H, hHn, hHae⟩ := timeDiff_extraction_ae2 hη0 hη4 hθ0 hθη hκc hκs G hfin
  let G' : (Fin 3 → ℝ) → V → ℂ := fun τ v =>
    if τ ∈ B3 ∧ v ∈ K then ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
          (F ![τ 0, τ 2] v - F ![τ 1, τ 2] v) else H τ v
  refine iInf_le_of_le G' (iInf_le_of_le (fun τ hτ v hv => by simp [G', hτ, hv]) ?_)
  rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00,
    NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  have hcongr : mixedFourierNorm00 θ G' = mixedFourierNorm00 θ H := by
    apply mixedFourierNorm00_congr_ae
    intro v
    filter_upwards [hHae] with τ hτ
    by_cases hc : τ ∈ B3 ∧ v ∈ K
    · simp only [G', if_pos hc]
      rw [hτ v, hκ1 τ (hR τ hc.1), hG _ (hB τ hc.1).1 v hc.2, hG _ (hB τ hc.1).2 v hc.2]
      ring
    · simp only [G', if_neg hc]
  rw [hcongr]
  refine hHn.trans ?_
  rw [hC, add_mul, one_mul]
  exact le_self_add


end WaveTurbulence.VineEstS4c.TimeDiff

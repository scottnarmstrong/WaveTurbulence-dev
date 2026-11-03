/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.CutoffBounds

/-!
# DH21 Lemma 6.3(1) on the square torus

Generic smooth compact spatial cutoffs are localized at arbitrary centers and
scales at least one. A single constant controls all positive cutoff scales,
both Fourier frequencies, all centers, and the principal-value limit.

We prove the estimate under weaker amplitude regularity than DH21
(NTphibounds): joint continuity, a supremum bound, and a Lipschitz bound in
the second momentum. The source's bounded first derivatives imply this
Lipschitz premise by the mean value theorem; no oscillatory-integral estimate
is assumed. The anisotropic `β` case is outside campaign ruling D2.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- DH21 Lemma 6.3(1), L1305–L1320, for the square-torus bilinear form.
The shared constant is chosen before every center, scale, frequency and amplitude. -/
theorem dh21_inverse_resonance_bound
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {ρ σ : Mom d → ℝ} (hρ : ContDiff ℝ 1 ρ) (hσ : ContDiff ℝ 1 σ)
    (hρc : HasCompactSupport ρ) (hσc : HasCompactSupport σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (D : ℝ≥0) (scale : ℝ), 1 ≤ scale →
      ∀ (a b : Mom d) (Θ : Mom d → Mom d → ℂ),
      Continuous (Function.uncurry Θ) → (∀ x y, ‖Θ x y‖ ≤ D) →
      (∀ x, LipschitzWith D (Θ x)) → ∀ ξ η : Mom d,
      (∀ μ : ℝ, 0 < μ →
        ‖bilinearFourierTruncation χ μ (localizedAmplitude ρ σ Θ scale a b) ξ η‖ ≤
          M * (D : ℝ) * scale ^ (2 * d)) ∧
      ∃ v : ℂ, Tendsto
        (fun μ => bilinearFourierTruncation χ μ (localizedAmplitude ρ σ Θ scale a b) ξ η)
        atTop (𝓝 v) ∧ ‖v‖ ≤ M * (D : ℝ) * scale ^ (2 * d) := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  obtain ⟨Bρ, hBρ⟩ := exists_nnreal_bound_cutoff hρ.continuous hρc
  obtain ⟨Bσ, hBσ⟩ := exists_nnreal_bound_cutoff hσ.continuous hσc
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiff_compact hσ hσc
  obtain ⟨rρ, hrρ, hsρ⟩ := exists_support_radius_cutoff hρc
  obtain ⟨rσ, _hrσ, hsσ⟩ := exists_support_radius_cutoff hσc
  let r : ℝ := max rρ rσ
  have hr : 1 ≤ r := hrρ.trans (le_max_left _ _)
  have hsρ' : ∀ z, r < ‖z‖ → ρ z = 0 := fun z hz => hsρ z ((le_max_left _ _).trans_lt hz)
  have hsσ' : ∀ z, r < ‖z‖ → σ z = 0 := fun z hz => hsσ z ((le_max_right _ _).trans_lt hz)
  let B : ℝ≥0 := Bρ * (Bσ + K + 1)
  let Q : ℝ := (B : ℝ) * bilinearFourierBoundConst d χ C * r ^ (2 * d)
  let M : ℝ := |Q| + 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro D scale hscale a b Θ hΘc hΘb hΘL ξ η
  have hsp : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hR : 1 ≤ r * scale := hr.trans (le_mul_of_one_le_right hr0 hscale)
  let A := localizedAmplitude ρ σ Θ scale a b
  have hAc : Continuous (Function.uncurry A) := continuous_localizedAmplitude hρ.continuous hσ.continuous hΘc scale a b
  have hAb : ∀ x y, ‖A x y‖ ≤ (B * D : ℝ≥0) :=
    fun x y => norm_localizedAmplitude_le hBρ hBσ hΘb scale a b x y
  have hAL : ∀ x, LipschitzWith (B * D) (A x) :=
    fun x => lipschitzWith_localizedAmplitude hBρ hBσ hK hΘb hΘL hscale a b x
  have hAx : ∀ x y, r * scale < ‖x - a‖ → A x y = 0 :=
    fun x y hx => localizedAmplitude_eq_zero_left hsp hsρ' a b x y hx
  have hAy : ∀ x y, r * scale < ‖y - b‖ → A x y = 0 :=
    fun x y hy => localizedAmplitude_eq_zero_right hsp hsσ' a b x y hy
  have hfinal : ((B * D : ℝ≥0) : ℝ) * bilinearFourierBoundConst d χ C * (r * scale) ^ (2 * d) ≤
      M * (D : ℝ) * scale ^ (2 * d) := by
    have he : ((B * D : ℝ≥0) : ℝ) * bilinearFourierBoundConst d χ C * (r * scale) ^ (2 * d) =
        Q * (D : ℝ) * scale ^ (2 * d) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    rw [he]
    have hQ : Q ≤ M := by dsimp [M]; linarith [le_abs_self Q]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ D.coe_nonneg) (by positivity)
  refine ⟨fun μ hμ => ?_, ?_⟩
  · exact (norm_bilinearFourierTruncation_le hd hχ hχs hC hμ hR hAL hAb hAx hAy ξ η).trans hfinal
  · obtain ⟨v, hv, hvb⟩ := exists_bilinearFourierTruncation_limit hd hχ hχs hC hR hAc hAL hAb hAx hAy ξ η
    exact ⟨v, hv, hvb.trans hfinal⟩

end WaveTurbulence.Resonant

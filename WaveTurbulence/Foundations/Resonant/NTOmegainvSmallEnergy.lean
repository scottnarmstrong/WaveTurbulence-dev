/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.CutoffBounds
public import WaveTurbulence.Foundations.Resonant.SmallEnergyBound
public import WaveTurbulence.Foundations.Resonant.SmallEnergyCharacterization

/-!
# DH21 Lemma 6.3(2) for generic scaled spatial cutoffs

The low-energy singularity is interpreted by a second cutoff and its proved
principal-value limit. One fixed constant controls the error by
`D scale^(2d) μ⁻¹ (1+|ξ|+|η|)`, uniformly in the spatial centers.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- DH21 Lemma 6.3(2), L1319–L1323, on the square torus. -/
theorem dh21_small_energy_bound
    (hd : 3 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {ρ σ : Mom d → ℝ} (hρ : ContDiff ℝ 1 ρ) (hσ : ContDiff ℝ 1 σ)
    (hρc : HasCompactSupport ρ) (hσc : HasCompactSupport σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (D : ℝ≥0) (scale : ℝ), 1 ≤ scale →
      ∀ (a b : Mom d) (Θ : Mom d → Mom d → ℂ),
      Continuous (Function.uncurry Θ) → (∀ x y, ‖Θ x y‖ ≤ D) →
      (∀ x, LipschitzWith D (Θ x)) → ∀ μ : ℝ, 0 < μ → ∀ ξ η : Mom d,
      ∃ v : ℂ, Tendsto
        (fun ν => lowBilinearFourierTruncation χ ν μ (localizedAmplitude ρ σ Θ scale a b) ξ η)
        atTop (𝓝 v) ∧
      ‖v‖ ≤ M * (D : ℝ) * scale ^ (2 * d) * μ⁻¹ * (1 + ‖ξ‖ + ‖η‖) := by
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
  let Q : ℝ := (B : ℝ) * smallEnergyBoundConst d χ * r ^ (2 * d)
  let M : ℝ := |Q| + 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hMpos, ?_⟩
  intro D scale hscale a b Θ hΘc hΘb hΘL μ hμ ξ η
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
  have hfinal : ((B * D : ℝ≥0) : ℝ) * smallEnergyBoundConst d χ * (r * scale) ^ (2 * d) ≤
      M * (D : ℝ) * scale ^ (2 * d) := by
    have he : ((B * D : ℝ≥0) : ℝ) * smallEnergyBoundConst d χ * (r * scale) ^ (2 * d) =
        Q * (D : ℝ) * scale ^ (2 * d) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    rw [he]
    have hQ : Q ≤ M := by dsimp [M]; linarith [le_abs_self Q]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ D.coe_nonneg) (by positivity)
  refine ⟨_, tendsto_lowBilinearFourierTruncation (by omega) hχ hχs hC hR hAc hAL hAb hAx hAy μ ξ η, ?_⟩
  refine (norm_bilinearFourier_small_energy_le hd hχ hχs hμ hR hAc hAL hAb hAx hAy ξ η).trans ?_
  have hfreq : 1 + ‖η‖ ≤ 1 + ‖ξ‖ + ‖η‖ := by linarith [norm_nonneg ξ]
  have hcoef : 0 ≤ M * (D : ℝ) * scale ^ (2 * d) * μ⁻¹ := by positivity
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfinal (inv_nonneg.mpr hμ.le)) (by positivity : 0 ≤ 1 + ‖η‖)).trans
      (mul_le_mul_of_nonneg_left hfreq hcoef)

end WaveTurbulence.Resonant

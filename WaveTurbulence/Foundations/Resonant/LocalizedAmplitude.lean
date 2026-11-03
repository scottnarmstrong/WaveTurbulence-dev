/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.BilinearFourierLimit

/-!
# The scaled spatial cutoffs in DH21 Lemma 6.3

The localized amplitude is `ρ((x-a)/scale) σ((y-b)/scale) Θ(x,y)`.
For `scale≥1`, scaling is a contraction. Fixed bounds and a Lipschitz constant for
`ρ,σ` therefore give amplitude bounds independent of both centers and `scale`.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence

variable {d : ℕ}

/-- Translation and inverse scaling of a momentum variable. -/
@[expose] noncomputable def cutoffScale (scale : ℝ) (b y : Mom d) : Mom d := scale⁻¹ • (y - b)

/-- The spatially localized amplitude of DH21 Lemma 6.3. -/
@[expose] noncomputable def localizedAmplitude (ρ σ : Mom d → ℝ)
    (Θ : Mom d → Mom d → ℂ) (scale : ℝ) (a b x y : Mom d) : ℂ :=
  (ρ (cutoffScale scale a x) : ℂ) * ((σ (cutoffScale scale b y) : ℂ) * Θ x y)

/-- At scales `scale≥1`, the scaled translation is a contraction. -/
theorem lipschitzWith_cutoffScale {scale : ℝ} (hscale : 1 ≤ scale) (b : Mom d) :
    LipschitzWith 1 (cutoffScale scale b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [cutoffScale, NNReal.coe_one, one_mul]
  rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (by linarith : 0 ≤ scale), ← dist_eq_norm]
  exact mul_le_of_le_one_left dist_nonneg (inv_le_one_of_one_le₀ hscale)

/-- A fixed spatial cutoff keeps the same Lipschitz constant after scaling. -/
theorem lipschitzWith_scaled_cutoff {σ : Mom d → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) {scale : ℝ} (hscale : 1 ≤ scale) (b : Mom d) :
    LipschitzWith K (fun y => σ (cutoffScale scale b y)) := by
  simpa only [mul_one, Function.comp_def] using hσ.comp (lipschitzWith_cutoffScale hscale b)

/-- Continuity in both momentum variables. -/
theorem continuous_localizedAmplitude {ρ σ : Mom d → ℝ} {Θ : Mom d → Mom d → ℂ}
    (hρ : Continuous ρ) (hσ : Continuous σ) (hΘ : Continuous (Function.uncurry Θ))
    (scale : ℝ) (a b : Mom d) :
    Continuous (Function.uncurry (localizedAmplitude ρ σ Θ scale a b)) := by
  have hl : Continuous (fun p : Mom d × Mom d => ρ (scale⁻¹ • (p.1 - a))) :=
    by fun_prop
  have hr : Continuous (fun p : Mom d × Mom d => σ (scale⁻¹ • (p.2 - b))) :=
    by fun_prop
  exact (Complex.continuous_ofReal.comp hl).mul ((Complex.continuous_ofReal.comp hr).mul hΘ)

/-- Uniform supremum bound for the localized amplitude. -/
theorem norm_localizedAmplitude_le {ρ σ : Mom d → ℝ} {Θ : Mom d → Mom d → ℂ}
    {Bρ Bσ K D : ℝ≥0} (hρ : ∀ x, |ρ x| ≤ Bρ) (hσ : ∀ y, |σ y| ≤ Bσ)
    (hΘ : ∀ x y, ‖Θ x y‖ ≤ D) (scale : ℝ) (a b x y : Mom d) :
    ‖localizedAmplitude ρ σ Θ scale a b x y‖ ≤ (Bρ * (Bσ + K + 1) * D : ℝ≥0) := by
  rw [localizedAmplitude, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have h : |ρ (cutoffScale scale a x)| * (|σ (cutoffScale scale b y)| * ‖Θ x y‖) ≤
      (Bρ : ℝ) * ((Bσ : ℝ) * (D : ℝ)) :=
    mul_le_mul (hρ _) (mul_le_mul (hσ _) (hΘ x y) (norm_nonneg _) Bσ.coe_nonneg)
    (mul_nonneg (abs_nonneg _) (norm_nonneg _)) Bρ.coe_nonneg
  refine h.trans ?_
  change (Bρ : ℝ) * ((Bσ : ℝ) * (D : ℝ)) ≤
    (Bρ : ℝ) * ((Bσ : ℝ) + (K : ℝ) + 1) * (D : ℝ)
  have hk : (Bσ : ℝ) ≤ (Bσ : ℝ) + (K : ℝ) + 1 := by linarith [K.coe_nonneg]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk D.coe_nonneg)
    Bρ.coe_nonneg).trans_eq (by ring)

/-- Lipschitz control of a product of bounded complex functions. -/
theorem lipschitzWith_mul_of_bounds {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℂ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
  rw [he]
  have hf' : ‖f x - f y‖ ≤ (Kf : ℝ) * dist x y := by simpa only [dist_eq_norm] using hf.dist_le_mul x y
  have hg' : ‖g x - g y‖ ≤ (Kg : ℝ) * dist x y := by simpa only [dist_eq_norm] using hg.dist_le_mul x y
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  exact (add_le_add
    (mul_le_mul (hfb x) hg' (norm_nonneg _) Bf.coe_nonneg)
    (mul_le_mul hf' (hgb y) (norm_nonneg _) (by positivity))).trans_eq (by push_cast; ring)

/-- Uniform normal Lipschitz bound for the localized amplitude. -/
theorem lipschitzWith_localizedAmplitude
    {ρ σ : Mom d → ℝ} {Θ : Mom d → Mom d → ℂ} {Bρ Bσ K D : ℝ≥0}
    (hρ : ∀ x, |ρ x| ≤ Bρ) (hσ : ∀ y, |σ y| ≤ Bσ) (hσL : LipschitzWith K σ)
    (hΘ : ∀ x y, ‖Θ x y‖ ≤ D) (hΘL : ∀ x, LipschitzWith D (Θ x))
    {scale : ℝ} (hscale : 1 ≤ scale) (a b x : Mom d) :
    LipschitzWith (Bρ * (Bσ + K + 1) * D) (localizedAmplitude ρ σ Θ scale a b x) := by
  have hσC : LipschitzWith K (fun y => (σ (cutoffScale scale b y) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (lipschitzWith_scaled_cutoff hσL hscale b)
  have hσB : ∀ y, ‖(σ (cutoffScale scale b y) : ℂ)‖ ≤ Bσ := fun y => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hσ _
  have hp := lipschitzWith_mul_of_bounds hσC (hΘL x) hσB (hΘ x)
  have hc : LipschitzWith 0 (fun _ : Mom d => (ρ (cutoffScale scale a x) : ℂ)) := LipschitzWith.const _
  have hρB : ∀ _ : Mom d, ‖(ρ (cutoffScale scale a x) : ℂ)‖ ≤ Bρ := fun _ => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ _
  have hpB : ∀ y, ‖(σ (cutoffScale scale b y) : ℂ) * Θ x y‖ ≤ (Bσ * D : ℝ≥0) := by
    intro y
    rw [norm_mul]
    simpa only [NNReal.coe_mul] using
      mul_le_mul (hσB y) (hΘ x y) (norm_nonneg _) Bσ.coe_nonneg
  have hfull := lipschitzWith_mul_of_bounds (Bg := Bσ * D) hc hp hρB hpB
  apply hfull.weaken
  simp only [zero_mul, add_zero]
  have hk : Bσ * D + K * D ≤ (Bσ + K + 1) * D := by
    rw [add_mul, add_mul, one_mul]
    exact le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ D from bot_le)
  exact (mul_le_mul_of_nonneg_left hk (show (0 : ℝ≥0) ≤ Bρ from bot_le)).trans_eq (by ring)

/-- Localization in the first spatial cutoff's support. -/
theorem localizedAmplitude_eq_zero_left
    {ρ σ : Mom d → ℝ} {Θ : Mom d → Mom d → ℂ} {r scale : ℝ}
    (hscale : 0 < scale) (hρ : ∀ z, r < ‖z‖ → ρ z = 0)
    (a b x y : Mom d) (hx : r * scale < ‖x - a‖) :
    localizedAmplitude ρ σ Θ scale a b x y = 0 := by
  have hz : r < ‖cutoffScale scale a x‖ := by
    rw [cutoffScale, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hscale, inv_mul_eq_div]
    exact (lt_div_iff₀ hscale).mpr hx
  simp only [localizedAmplitude, hρ _ hz, Complex.ofReal_zero, zero_mul]

/-- Localization in the second spatial cutoff's support. -/
theorem localizedAmplitude_eq_zero_right
    {ρ σ : Mom d → ℝ} {Θ : Mom d → Mom d → ℂ} {r scale : ℝ}
    (hscale : 0 < scale) (hσ : ∀ z, r < ‖z‖ → σ z = 0)
    (a b x y : Mom d) (hy : r * scale < ‖y - b‖) :
    localizedAmplitude ρ σ Θ scale a b x y = 0 := by
  have hz : r < ‖cutoffScale scale b y‖ := by
    rw [cutoffScale, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hscale, inv_mul_eq_div]
    exact (lt_div_iff₀ hscale).mpr hy
  simp only [localizedAmplitude, hσ _ hz, Complex.ofReal_zero, zero_mul, mul_zero]

end WaveTurbulence

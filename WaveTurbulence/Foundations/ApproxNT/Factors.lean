/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Core
public import WaveTurbulence.Foundations.ApproxNT.CellMinor

/-!
# Rescaled one-cell factors (packet NT6)

In the decoupled representation `∫ Φ̂(s) ∏ᵢ cellSum(μ sᵢ) ds` every factor is a function of one
time variable `t = sᵢ`. This file records the one-cell estimates in the rescaled variable
`t ↦ μ t`, each gaining the factor `μ⁻¹`:

* `∫ |φ(μt) S(μt)| ≲ μ⁻¹ L^{2d}`, `∫ |φ(μt) L^{2d}T(μt)| ≲ μ⁻¹ L^{2d}`, `∫ |L^{2d}T(μt)| ≲ μ⁻¹ L^{2d}`;
* `∫ |φ(μt) L^{2d}N(μt)| ≲ μ⁻¹ L^{2d} L^{-1+2η}(1+|ξ|+|ζ|)` (DH23 Lemma 6.5(2));
* `∫ |(1-φ)(μt) L^{2d}T(μt)| ≲ μ⁻¹ L^{2d} L^{-1}` (stationary phase);
* `∫ ⟨t⟩^{-2d} |(1-φ)(μt) S(μt)| ≲ μ⁻¹ L^{2d} L^{-2(d-1)(1-γ)+η}` (DH23 Lemma 6.6(2), `μ = δL^{2γ}`).
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

theorem lintegral_comp_mul {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, f (μ * t) = ENNReal.ofReal μ⁻¹ * ∫⁻ u, f u := by
  have h := NTSP.lintegral_comp_affine hμ.ne' 0 hf
  simp only [zero_add, abs_of_pos hμ] at h
  rw [← h]
  congr 1; funext t; rw [mul_comm]

/-- The polynomial time weight `⟨t⟩^{-2d}` becomes the source's weight `⟨s/μ⟩^{-2d}`. -/
theorem japaneseTimeWeight_rescale {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    WeylSums.japaneseTimeWeight μ (2 * d) (μ * t) = ((1 + t ^ 2) ^ d)⁻¹ := by
  rw [WeylSums.japaneseTimeWeight, mul_div_cancel_left₀ _ hμ.ne']
  rw [show -(2 * (d : ℝ)) / 2 = -(d : ℝ) by ring, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- The rescaled cell sum. -/
@[expose] def scS (L μ : ℝ) (p q ξ ζ : Mom d) (t : ℝ) : ℂ := cellSum L p q ξ ζ (μ * t)

/-- The rescaled cell integral, times `L^{2d}`. -/
@[expose] def scT (L μ : ℝ) (p q ξ ζ : Mom d) (t : ℝ) : ℂ :=
  ((L ^ (2 * d) : ℝ) : ℂ) * cellInt p q ξ ζ (μ * t)

/-- The rescaled nonzero modes, times `L^{2d}`. -/
@[expose] def scN (L μ : ℝ) (p q ξ ζ : Mom d) (t : ℝ) : ℂ :=
  ((L ^ (2 * d) : ℝ) : ℂ) * cellModes L p q ξ ζ (μ * t)

/-- The rescaled cutoffs. -/
@[expose] def scMaj (L μ t : ℝ) : ℂ := majorCut L (μ * t)

@[expose] def scMin (L μ t : ℝ) : ℂ := minorCut L (μ * t)

theorem scMaj_add_scMin (L μ t : ℝ) : scMaj L μ t + scMin L μ t = 1 := majorCut_add_minorCut _ _

theorem scS_eq {L : ℝ} (hL : 0 < L) (μ : ℝ) (p q ξ ζ : Mom d) (t : ℝ) :
    scS L μ p q ξ ζ t = scT L μ p q ξ ζ t + scN L μ p q ξ ζ t := by
  rw [scS, scT, scN, cellSum_eq_modes hL, mul_add]

theorem continuous_scS {L : ℝ} (hL : 0 < L) (μ : ℝ) (p q ξ ζ : Mom d) :
    Continuous (scS L μ p q ξ ζ) :=
  (continuous_cellSum hL p q ξ ζ).comp (continuous_const.mul continuous_id)

theorem continuous_scT (L μ : ℝ) (p q ξ ζ : Mom d) : Continuous (scT L μ p q ξ ζ) :=
  continuous_const.mul ((continuous_cellInt p q ξ ζ).comp (continuous_const.mul continuous_id))

theorem continuous_scN {L : ℝ} (hL : 0 < L) (μ : ℝ) (p q ξ ζ : Mom d) :
    Continuous (scN L μ p q ξ ζ) := by
  have h : scN L μ p q ξ ζ = fun t => scS L μ p q ξ ζ t - scT L μ p q ξ ζ t := by
    funext t; rw [scS_eq hL]; ring
  rw [h]; exact (continuous_scS hL μ p q ξ ζ).sub (continuous_scT L μ p q ξ ζ)

theorem continuous_scMaj (L μ : ℝ) : Continuous (scMaj L μ) :=
  (continuous_majorCut L).comp (continuous_const.mul continuous_id)

theorem continuous_scMin (L μ : ℝ) : Continuous (scMin L μ) :=
  (continuous_minorCut L).comp (continuous_const.mul continuous_id)

theorem enorm_Lpow (L : ℝ) (hL : 0 ≤ L) (z : ℂ) :
    ‖((L ^ (2 * d) : ℝ) : ℂ) * z‖ₑ = ENNReal.ofReal (L ^ (2 * d)) * ‖z‖ₑ := by
  rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- `∫ |L^{2d} T(μt)| ≲ μ⁻¹ L^{2d}`. -/
theorem lintegral_scT_le (hd : 2 ≤ d) {L μ : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ) (p q ξ ζ : Mom d) :
    ∫⁻ t, ‖scT L μ p q ξ ζ t‖ₑ ≤
      ENNReal.ofReal (μ⁻¹ * L ^ (2 * d) * (cellK0 d * NTSP.sInt d)) := by
  simp_rw [scT, enorm_Lpow L hL]
  have hc := lintegral_comp_mul hμ (continuous_cellInt p q ξ ζ).enorm.measurable
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hc]
  calc ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ * ∫⁻ u, ‖cellInt p q ξ ζ u‖ₑ)
      ≤ ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ *
          ENNReal.ofReal (cellK0 d * NTSP.sInt d)) := by
        gcongr; exact lintegral_cellInt_le hd p q ξ ζ
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hμ.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- `∫ |φ(μt) L^{2d} T(μt)| ≲ μ⁻¹ L^{2d}`. -/
theorem lintegral_scMaj_scT_le (hd : 2 ≤ d) {L μ : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ)
    (p q ξ ζ : Mom d) :
    ∫⁻ t, ‖scMaj L μ t * scT L μ p q ξ ζ t‖ₑ ≤
      ENNReal.ofReal (μ⁻¹ * L ^ (2 * d) * (cellK0 d * NTSP.sInt d)) := by
  refine (lintegral_mono fun t => ?_).trans (lintegral_scT_le hd hL hμ p q ξ ζ)
  rw [enorm_mul]
  calc ‖scMaj L μ t‖ₑ * ‖scT L μ p q ξ ζ t‖ₑ ≤ 1 * ‖scT L μ p q ξ ζ t‖ₑ := by
        gcongr
        rw [← ofReal_norm, ENNReal.ofReal_le_one]; exact norm_majorCut_le _ _
    _ = _ := one_mul _

/-- The major-arc tail: `∫ |(1-φ)(μt) L^{2d} T(μt)| ≲ μ⁻¹ L^{2d} L^{-1}`. -/
theorem lintegral_scMin_scT_le (hd : 3 ≤ d) {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    (p q ξ ζ : Mom d) :
    ∫⁻ t, ‖scMin L μ t * scT L μ p q ξ ζ t‖ₑ ≤
      ENNReal.ofReal (μ⁻¹ * L ^ (2 * d) * (cellK0 d * NTSP.sInt (d - 1) * L⁻¹)) := by
  have hrw : ∀ t, ‖scMin L μ t * scT L μ p q ξ ζ t‖ₑ =
      ENNReal.ofReal (L ^ (2 * d)) * ‖minorCut L (μ * t) * cellInt p q ξ ζ (μ * t)‖ₑ := by
    intro t
    rw [scMin, scT, mul_left_comm, enorm_Lpow L hL.le]
  simp_rw [hrw]
  have hm : Measurable fun u => ‖minorCut L u * cellInt p q ξ ζ u‖ₑ :=
    ((continuous_minorCut L).mul (continuous_cellInt p q ξ ζ)).enorm.measurable
  have hc := lintegral_comp_mul hμ hm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hc]
  calc ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ *
        ∫⁻ u, ‖minorCut L u * cellInt p q ξ ζ u‖ₑ)
      ≤ ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ *
          ENNReal.ofReal (cellK0 d * L⁻¹ * NTSP.sInt (d - 1))) := by
        gcongr; exact lintegral_minorCut_cellInt_le hd hL p q ξ ζ
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hμ.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- (NTSPest2) rescaled: `∫ |φ(μt) S(μt)| ≲ μ⁻¹ L^{2d}`. -/
theorem exists_lintegral_scMaj_scS_le (hd : 3 ≤ d) {η : ℝ} (hη : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L μ : ℝ, 1 ≤ L → 2 ≤ L ^ η → 0 < μ → ∀ p q ξ ζ : Mom d,
      ∫⁻ t, ‖scMaj L μ t * scS L μ p q ξ ζ t‖ₑ ≤ ENNReal.ofReal (μ⁻¹ * L ^ (2 * d) * C) := by
  obtain ⟨C, hC0, hC⟩ := exists_lintegral_major_le hd hη
  refine ⟨C, hC0, fun L μ hL hLη hμ p q ξ ζ => ?_⟩
  have hL0 : 0 < L := by linarith
  have hrw : ∀ t, ‖scMaj L μ t * scS L μ p q ξ ζ t‖ₑ = ENNReal.ofReal (L ^ (2 * d)) *
      ‖majorCut L (μ * t) * (cellInt p q ξ ζ (μ * t) + cellModes L p q ξ ζ (μ * t))‖ₑ := by
    intro t
    rw [scMaj, scS, cellSum_eq_modes hL0, mul_left_comm, enorm_Lpow L hL0.le]
  simp_rw [hrw]
  have hm : Measurable fun u => ‖majorCut L u * (cellInt p q ξ ζ u + cellModes L p q ξ ζ u)‖ₑ := by
    have hmod : Continuous (cellModes L p q ξ ζ) :=
      (continuous_const.mul (continuous_cellSum hL0 p q ξ ζ)).sub (continuous_cellInt p q ξ ζ)
    exact ((continuous_majorCut L).mul ((continuous_cellInt p q ξ ζ).add hmod)).enorm.measurable
  have hc := lintegral_comp_mul hμ hm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hc]
  calc ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ * ∫⁻ u,
        ‖majorCut L u * (cellInt p q ξ ζ u + cellModes L p q ξ ζ u)‖ₑ)
      ≤ ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ * ENNReal.ofReal C) := by
        gcongr; exact hC L hL hLη p q ξ ζ
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hμ.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- (NTSPest2) rescaled, in the form `φ (T + N)`. -/
theorem lintegral_scMaj_scTN_eq {L : ℝ} (hL : 0 < L) (μ : ℝ) (p q ξ ζ : Mom d) :
    ∫⁻ t, ‖scMaj L μ t * (scT L μ p q ξ ζ t + scN L μ p q ξ ζ t)‖ₑ =
      ∫⁻ t, ‖scMaj L μ t * scS L μ p q ξ ζ t‖ₑ := by
  simp_rw [scS_eq hL]

/-- DH23 Lemma 6.5(2) rescaled: `∫ |φ(μt) L^{2d}N(μt)| ≲ μ⁻¹ L^{2d} L^{-1+2η}(1+|ξ|+|ζ|)`. -/
theorem exists_lintegral_scMaj_scN_le (hd : 3 ≤ d) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L μ : ℝ, 1 ≤ L → 2 ≤ L ^ η → 0 < μ → ∀ p q ξ ζ : Mom d,
      ∫⁻ t, ‖scMaj L μ t * scN L μ p q ξ ζ t‖ₑ ≤
        ENNReal.ofReal (μ⁻¹ * L ^ (2 * d) * (C * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖))) := by
  obtain ⟨C, hC0, hC⟩ := exists_lintegral_modes_le hd hη0 hη
  refine ⟨C, hC0, fun L μ hL hLη hμ p q ξ ζ => ?_⟩
  have hL0 : 0 < L := by linarith
  have hrw : ∀ t, ‖scMaj L μ t * scN L μ p q ξ ζ t‖ₑ = ENNReal.ofReal (L ^ (2 * d)) *
      ‖majorCut L (μ * t) * cellModes L p q ξ ζ (μ * t)‖ₑ := by
    intro t
    rw [scMaj, scN, mul_left_comm, enorm_Lpow L hL0.le]
  simp_rw [hrw]
  have hm : Measurable fun u => ‖majorCut L u * cellModes L p q ξ ζ u‖ₑ := by
    have hmod : Continuous (cellModes L p q ξ ζ) :=
      (continuous_const.mul (continuous_cellSum hL0 p q ξ ζ)).sub (continuous_cellInt p q ξ ζ)
    exact ((continuous_majorCut L).mul hmod).enorm.measurable
  have hc := lintegral_comp_mul hμ hm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hc]
  calc ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ *
        ∫⁻ u, ‖majorCut L u * cellModes L p q ξ ζ u‖ₑ)
      ≤ ENNReal.ofReal (L ^ (2 * d)) * (ENNReal.ofReal μ⁻¹ *
          ENNReal.ofReal (C * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖))) := by
        gcongr; exact hC L hL hLη p q ξ ζ
    _ = _ := by
        have : 0 ≤ C * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖) := by
          have := Real.rpow_nonneg hL0.le (-1 + 2 * η); positivity
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hμ.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- DH23 Lemma 6.6(2) rescaled. -/
theorem exists_lintegral_scMin_scS_le (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L δ : ℝ, 2 ≤ L → δ ∈ Ioc (0 : ℝ) 1 → ∀ p q ξ ζ : Mom d,
      ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ d)⁻¹ *
          ‖scMin L (δ * L ^ (2 * γ)) t * scS L (δ * L ^ (2 * γ)) p q ξ ζ t‖ₑ ≤
        ENNReal.ofReal ((δ * L ^ (2 * γ))⁻¹ * L ^ (2 * d) *
          (C * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η))) := by
  obtain ⟨C, hC0, hC⟩ := exists_lintegral_minor_le hd hγ hη
  refine ⟨C, hC0, fun L δ hL hδ p q ξ ζ => ?_⟩
  have hL0 : 0 < L := by linarith
  set μ := δ * L ^ (2 * γ) with hμdef
  have hμ : 0 < μ := mul_pos hδ.1 (Real.rpow_pos_of_pos hL0 _)
  have hrw : ∀ t, ENNReal.ofReal ((1 + t ^ 2) ^ d)⁻¹ * ‖scMin L μ t * scS L μ p q ξ ζ t‖ₑ =
      (fun u => ENNReal.ofReal (WeylSums.japaneseTimeWeight μ (2 * d) u) *
        ‖minorCut L u * cellSum L p q ξ ζ u‖ₑ) (μ * t) := by
    intro t
    simp only [scMin, scS]
    rw [japaneseTimeWeight_rescale hμ]
  simp_rw [hrw]
  have hm : Measurable fun u => ENNReal.ofReal (WeylSums.japaneseTimeWeight μ (2 * d) u) *
      ‖minorCut L u * cellSum L p q ξ ζ u‖ₑ :=
    (ENNReal.measurable_ofReal.comp (WeylSums.continuous_japaneseTimeWeight μ (2 * d)).measurable).mul
      ((continuous_minorCut L).mul (continuous_cellSum hL0 p q ξ ζ)).enorm.measurable
  rw [lintegral_comp_mul hμ hm]
  calc ENNReal.ofReal μ⁻¹ * ∫⁻ u, ENNReal.ofReal (WeylSums.japaneseTimeWeight μ (2 * d) u) *
        ‖minorCut L u * cellSum L p q ξ ζ u‖ₑ
      ≤ ENNReal.ofReal μ⁻¹ * ENNReal.ofReal
          (C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)) := by
        gcongr; exact hC L hL δ hδ p q ξ ζ
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hμ.le)]
        congr 1
        have hsplit : L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) =
            L ^ (2 * d) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
          congr 1; push_cast; ring
        rw [hsplit]; ring

end WaveTurbulence.ApproxNT

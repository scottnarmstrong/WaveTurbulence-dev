/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueFourier

/-!
# The complex symmetric quotient

The quotient `(f(u)-f(-u))/(2u)` is integrable for an integrable Lipschitz test
function and is bounded by its Lipschitz constant. It provides the quantitative
small-energy error in DH21 Lemma 6.3(2).
-/

public section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace WaveTurbulence

/-- The symmetric cancellation quotient, interpreted by the displayed algebraic formula. -/
@[expose] noncomputable def symmetricQuotient (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (((2 * u)⁻¹ : ℝ) : ℂ) * (f u - f (-u))

/-- The quotient is the average of the integrable remainder and its reflection. -/
theorem symmetricQuotient_eq_remainder (f : ℝ → ℂ) (u : ℝ) :
    symmetricQuotient f u = (2 : ℂ)⁻¹ * (pvRemainder f u + pvRemainder f (-u)) := by
  have he : (Icc (-1 : ℝ) 1).indicator (fun _ => f 0) (-u) =
      (Icc (-1 : ℝ) 1).indicator (fun _ => f 0) u := by
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · have hn : -u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      rw [indicator_of_mem hu, indicator_of_mem hn]
    · have hn : -u ∉ Icc (-1 : ℝ) 1 := by
        intro h
        exact hu ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_notMem hu, indicator_of_notMem hn]
  simp only [symmetricQuotient, pvRemainder, he, Complex.real_smul, mul_inv, inv_neg]
  push_cast
  ring

/-- Lipschitz cancellation removes the singularity uniformly on the entire line. -/
theorem norm_symmetricQuotient_le {f : ℝ → ℂ} {K : ℝ≥0} (hL : LipschitzWith K f) (u : ℝ) :
    ‖symmetricQuotient f u‖ ≤ K := by
  by_cases hu : u = 0
  · simp [symmetricQuotient, hu]
  · rw [symmetricQuotient, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), inv_mul_eq_div,
      div_le_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hu))]
    simpa only [dist_eq_norm, Real.norm_eq_abs, sub_neg_eq_add, ← two_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hL.dist_le_mul u (-u)

/-- Integrability follows from the integrable remainder decomposition. -/
theorem integrable_symmetricQuotient {f : ℝ → ℂ} {K : ℝ≥0}
    (hf : Integrable f) (hL : LipschitzWith K f) : Integrable (symmetricQuotient f) := by
  have hi := integrable_pvRemainder hf hL
  have hh := (hi.add hi.comp_neg).const_mul ((2 : ℂ)⁻¹)
  exact hh.congr (Eventually.of_forall fun u => (symmetricQuotient_eq_remainder f u).symm)

/-- Exact cancellation at every finite scale, for an integrable Lipschitz amplitude. -/
theorem pvTruncationComplex_eq_symmetricQuotient {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} (hf : Integrable f) (μ : ℝ) :
    pvTruncationComplex χ μ f = ∫ u : ℝ, ((1 - χ (μ * u) : ℝ) : ℂ) * symmetricQuotient f u := by
  let q : ℝ → ℝ := fun u => (1 - χ (μ * u)) / u
  obtain ⟨C, _, hC⟩ := hχ.exists_bound_div μ
  have hqc : Continuous (fun u : ℝ => (q u : ℂ)) :=
    Complex.continuous_ofReal.comp (hχ.continuous_div μ)
  have hi : Integrable (fun u : ℝ => (q u : ℂ) * f u) := by
    have hh := hf.mul_bdd (g := fun u => (q u : ℂ)) (c := C) hqc.aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hC u)
    exact hh.congr (Eventually.of_forall fun u => mul_comm _ _)
  have hni : Integrable (fun u : ℝ => (q u : ℂ) * f (-u)) := by
    have hh := hf.comp_neg.mul_bdd (g := fun u => (q u : ℂ)) (c := C) hqc.aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hC u)
    exact hh.congr (Eventually.of_forall fun u => mul_comm _ _)
  have hodd : ∀ u, q (-u) = -q u := by
    intro u
    dsimp [q]
    rw [mul_neg, hχ.even, div_neg]
  have href : (∫ u : ℝ, (q u : ℂ) * f (-u)) = -(∫ u : ℝ, (q u : ℂ) * f u) := by
    have h := integral_neg_eq_self (fun u : ℝ => (q u : ℂ) * f (-u)) volume
    simp only [hodd, neg_neg, Complex.ofReal_neg, neg_mul, integral_neg] at h
    exact h.symm
  have heq : (∫ u : ℝ, ((1 - χ (μ * u) : ℝ) : ℂ) * symmetricQuotient f u) =
      (2 : ℂ)⁻¹ * ((∫ u : ℝ, (q u : ℂ) * f u) - ∫ u : ℝ, (q u : ℂ) * f (-u)) := by
    rw [← integral_sub hi hni, ← integral_const_mul]
    congr 1
    funext u
    simp only [symmetricQuotient, q, div_eq_mul_inv, mul_inv]
    push_cast
    ring
  rw [heq, href]
  unfold pvTruncationComplex
  change (∫ u : ℝ, (q u : ℂ) * f u) = _
  ring

/-- Principal-value convergence to the integrable symmetric quotient. -/
theorem tendsto_pvTruncationComplex_of_lipschitz {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} {K : ℝ≥0} (hf : Integrable f) (hL : LipschitzWith K f) :
    Tendsto (fun μ => pvTruncationComplex χ μ f) atTop
      (𝓝 (∫ u : ℝ, symmetricQuotient f u)) := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  have hi := integrable_symmetricQuotient hf hL
  have ht : Tendsto (fun μ : ℝ => ∫ u : ℝ,
      ((1 - χ (μ * u) : ℝ) : ℂ) * symmetricQuotient f u) atTop
      (𝓝 (∫ u : ℝ, symmetricQuotient f u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (1 + C) * ‖symmetricQuotient f u‖) ?_ ?_ (hi.norm.const_mul _) ?_
    · exact Eventually.of_forall fun μ =>
        (Complex.continuous_ofReal.comp
          (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable.mul
            hi.aestronglyMeasurable
    · refine Eventually.of_forall fun μ => Eventually.of_forall fun u => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        ((abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * u)) 1)) (norm_nonneg _)
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
      have hne : u ≠ 0 := by simpa using hu
      apply tendsto_const_nhds.congr'
      filter_upwards [hχ.eventually_comp_eq_zero hne] with μ hμ
      simp only [hμ, sub_zero, Complex.ofReal_one, one_mul]
  exact ht.congr fun μ => (pvTruncationComplex_eq_symmetricQuotient hχ hf μ).symm

/-- Quantitative small-energy error for a Lipschitz test function. -/
theorem norm_pvTruncationComplex_error_le {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} {K : ℝ≥0} (hf : Integrable f) (hL : LipschitzWith K f)
    {μ : ℝ} (hμ : 0 < μ) :
    ‖(∫ u : ℝ, symmetricQuotient f u) - pvTruncationComplex χ μ f‖ ≤
      (K : ℝ) * μ⁻¹ * ∫ u : ℝ, |χ u| := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  have hi := integrable_symmetricQuotient hf hL
  have hic : Integrable (fun u : ℝ => ((1 - χ (μ * u) : ℝ) : ℂ) * symmetricQuotient f u) := by
    have hh := hi.mul_bdd (g := fun u => ((1 - χ (μ * u) : ℝ) : ℂ)) (c := 1 + C)
      (Complex.continuous_ofReal.comp
        (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * u)) 1))
    exact hh.congr (Eventually.of_forall fun _ => mul_comm _ _)
  have he : (∫ u : ℝ, symmetricQuotient f u) - pvTruncationComplex χ μ f =
      ∫ u : ℝ, (χ (μ * u) : ℂ) * symmetricQuotient f u := by
    rw [pvTruncationComplex_eq_symmetricQuotient hχ hf μ, ← integral_sub hi hic]
    congr 1
    funext u
    push_cast
    ring
  have hχi : Integrable χ := hχ.cont.integrable_of_hasCompactSupport hχ.compact
  have hscaled := (hχi.comp_mul_left' hμ.ne').abs
  rw [he]
  calc ‖∫ u : ℝ, (χ (μ * u) : ℂ) * symmetricQuotient f u‖
      ≤ ∫ u : ℝ, |χ (μ * u)| * (K : ℝ) := by
        apply norm_integral_le_of_norm_le (hscaled.mul_const _) (Eventually.of_forall fun u => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_symmetricQuotient_le hL u) (abs_nonneg _)
    _ = (K : ℝ) * μ⁻¹ * ∫ u : ℝ, |χ u| := by
      rw [integral_mul_const, Measure.integral_comp_mul_left (fun u : ℝ => |χ u|) μ,
        smul_eq_mul, abs_of_pos (inv_pos.mpr hμ)]
      ring

end WaveTurbulence

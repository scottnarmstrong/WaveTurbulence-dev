/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.ComplexDualPower
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-!
# Localized `Lᵖ` duality for complex functions

Testing against an indicator times a complex dual power bounds the `L^q`
norm on any finite-measure set. The test functions belong to both `L¹`
and `Lᵖ`, so the ordinary integral Fourier pairing suffices.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- A uniformly bounded measurable function restricted to a finite-measure set
belongs to every `Lᵖ`, including the endpoints. -/
theorem memLp_indicator_of_uniform_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (p : ℝ≥0∞) :
    MemLp (s.indicator f) p μ := by
  have hc : MemLp (s.indicator (fun _ => M)) p μ :=
    memLp_indicator_const p hs.nullMeasurableSet M (Or.inr hμs)
  apply hc.mono' (hf.indicator hs)
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ s <;> simp [hx, hM x]

/-- A testing bound against `L¹ ∩ Lᵖ` controls the local `L^q` norm.
This is a general duality helper; the Fourier testing estimate is proved separately. -/
theorem eLpNorm_indicator_le_of_pairing {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → ℂ} (hf : Measurable f) {M : ℝ} (hfM : ∀ x, ‖f x‖ ≤ M)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ g : α → ℂ, Integrable g μ → MemLp g (ENNReal.ofReal p) μ →
      ‖∫ x, f x * g x ∂μ‖ ≤ C * lpNorm g (ENNReal.ofReal p) μ)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    eLpNorm (s.indicator f) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
  let g := s.indicator (fun x => complexDualPower q (f x))
  let A := ∫ x in s, ‖f x‖ ^ q ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hdual : Measurable (fun x => complexDualPower q (f x)) :=
    (complexDualPower_measurable q).comp hf
  have hdualM (x : α) : ‖complexDualPower q (f x)‖ ≤ M ^ (q - 1) := by
    rw [norm_complexDualPower hpq.symm.lt]
    exact Real.rpow_le_rpow (norm_nonneg _) (hfM x) (by linarith [hpq.symm.lt])
  have hg (r : ℝ≥0∞) : MemLp g r μ :=
    memLp_indicator_of_uniform_bound hs hμs hdual.aestronglyMeasurable hdualM r
  have hgnorm : lpNorm g (ENNReal.ofReal p) μ = A ^ p⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.pos)) ENNReal.ofReal_ne_top
      (hg (ENNReal.ofReal p)).aestronglyMeasurable, ENNReal.toReal_ofReal hpq.nonneg]
    have he (x : α) : ‖g x‖ ^ p = s.indicator (fun x => ‖f x‖ ^ q) x := by
      by_cases hx : x ∈ s
      · simp only [g, indicator_of_mem hx, norm_complexDualPower hpq.symm.lt,
          ← Real.rpow_mul (norm_nonneg _), hpq.symm.sub_one_mul_conj]
      · simp [g, hx, Real.zero_rpow hpq.ne_zero]
    simp_rw [he]
    rw [integral_indicator hs]
  have hpair : ‖∫ x, f x * g x ∂μ‖ = A := by
    have he (x : α) : f x * g x = s.indicator (fun x => ((‖f x‖ ^ q : ℝ) : ℂ)) x := by
      by_cases hx : x ∈ s
      · simp only [g, indicator_of_mem hx, mul_complexDualPower hpq.symm.lt]
      · simp [g, hx]
    simp_rw [he]
    rw [integral_indicator hs, integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg hA]
  have hbound : A ≤ C * A ^ p⁻¹ := by
    simpa only [hpair, hgnorm] using htest g (memLp_one_iff_integrable.mp (hg 1)) (hg _)
  have hroot : A ^ q⁻¹ ≤ C := by
    by_cases hz : A = 0
    · simpa only [hz, Real.zero_rpow (inv_ne_zero hpq.symm.ne_zero)] using hC
    have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    calc
      A ^ q⁻¹ = A ^ (1 - p⁻¹) := by rw [hpq.one_sub_inv]
      _ = A / A ^ p⁻¹ := by rw [Real.rpow_sub hpos, Real.rpow_one]
      _ ≤ C := (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).mpr (by simpa [mul_comm] using hbound)
  have hsf : MemLp (s.indicator f) (ENNReal.ofReal q) μ :=
    memLp_indicator_of_uniform_bound hs hμs hf.aestronglyMeasurable hfM _
  rw [← ofReal_lpNorm hsf]
  apply ENNReal.ofReal_le_ofReal
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.symm.pos)) ENNReal.ofReal_ne_top
    hsf.aestronglyMeasurable, ENNReal.toReal_ofReal hpq.symm.nonneg]
  have he (x : α) : ‖s.indicator f x‖ ^ q = s.indicator (fun x => ‖f x‖ ^ q) x := by
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, Real.zero_rpow hpq.symm.ne_zero]
  simp_rw [he]
  rw [integral_indicator hs]
  exact hroot

end WaveTurbulence.Fourier

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # A positive short-time Fourier kernel for counting energy bands -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The Fourier transform of a symmetric time interval. Its squared norm
will be the nonnegative majorant of a prescribed energy band. -/
@[expose] noncomputable def intervalFourierKernel (h E : ℝ) : ℂ :=
  ∫ s in Icc (-h) h, e (s*E)

/-- A fixed neighborhood of the origin where the real part of the
additive character is positive, obtained directly from continuity. -/
theorem exists_e_real_part_lower_bound :
    ∃ r : ℝ, 0 < r ∧ 2*r ≤ 1 ∧ ∀ x : ℝ, |x| ≤ r → (1 : ℝ)/2 ≤ (e x).re := by
  have hc : ContinuousAt (fun x : ℝ => (e x).re) 0 := (Complex.continuous_re.comp continuous_e).continuousAt
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  let r := min (δ/2) (1/4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  refine ⟨r,hr,by have hh := min_le_right (δ/2) (1/4 : ℝ); dsimp [r]; linarith,?_⟩
  intro x hx
  have hdist : dist x 0 < δ := by
    rw [Real.dist_eq,sub_zero]
    have hh := min_le_left (δ/2) (1/4 : ℝ)
    linarith
  have hh := hb hdist
  simp only [e_zero,Complex.one_re,Real.dist_eq] at hh
  have hl := (abs_lt.mp hh).1
  linarith

/-- The squared interval transform is bounded below uniformly on the
energy band after choosing its inverse bandwidth scale. -/
theorem exists_intervalFourierKernel_lower_bound :
    ∃ r : ℝ, 0 < r ∧ 2*r ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → ∀ E : ℝ, |E| ≤ τ →
      r/τ ≤ ‖intervalFourierKernel (r/τ) E‖ := by
  obtain ⟨r,hr,hrsmall,hre⟩ := exists_e_real_part_lower_bound
  refine ⟨r,hr,hrsmall,?_⟩
  intro τ hτ E hE
  let h := r/τ
  have hh : 0 < h := div_pos hr hτ
  have hi : IntegrableOn (fun s : ℝ => e (s*E)) (Icc (-h) h) :=
    (continuous_e.comp (by fun_prop)).continuousOn.integrableOn_Icc
  have hphase (s : ℝ) (hs : s ∈ Icc (-h) h) : (1 : ℝ)/2 ≤ (e (s*E)).re := by
    apply hre
    rw [abs_mul]
    have hsabs : |s| ≤ h := abs_le.mpr hs
    have hp := mul_le_mul hsabs hE (abs_nonneg E) hh.le
    have heq : h*τ = r := by dsimp [h]; field_simp
    exact hp.trans_eq heq
  have hconst : (∫ _s in Icc (-h) h, (1 : ℝ)/2) = h := by
    rw [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ h-(-h)),smul_eq_mul]
    ring
  have hRe : h ≤ (intervalFourierKernel h E).re := by
    have hreint : (∫ s in Icc (-h) h, (e (s*E)).re) = (∫ s in Icc (-h) h, e (s*E)).re := integral_re hi
    have hiRe : IntegrableOn (fun s => (e (s*E)).re) (Icc (-h) h) := hi.re
    calc
      h = ∫ _s in Icc (-h) h, (1 : ℝ)/2 := hconst.symm
      _ ≤ ∫ s in Icc (-h) h, (e (s*E)).re := by
        apply integral_mono_ae (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hiRe
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hphase s hs
      _ = (intervalFourierKernel h E).re := hreint
  exact hRe.trans (Complex.re_le_norm _)

end WaveTurbulence.WeylSums

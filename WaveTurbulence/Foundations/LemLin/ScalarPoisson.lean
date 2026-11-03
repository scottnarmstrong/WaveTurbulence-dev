/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.PoissonLattice
public import WaveTurbulence.Foundations.Fourier.CutoffFourierDecay
public import WaveTurbulence.Foundations.Fourier.NonstationaryPhase
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Scalar cutoff sums and Poisson majorants

TARGET `lemlin`, L1541. We use the negative Fourier sign for the scalar
frequency; the source sum is recovered by negating that frequency. This makes
the Poisson majorant a periodization at `u + Lm` without reflecting its argument.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff ENNReal

/-- Translated cutoff with a scalar linear modulation. -/
@[expose] noncomputable def scalarAmplitude (a u x : ℝ) : ℂ :=
  Fourier.chi0Complex (x - a) * (Real.fourierChar (-u * x) : ℂ)

/-- The scalar cutoff sum in the negative-frequency convention. -/
@[expose] noncomputable def scalarLatticeSum (L a u : ℝ) : ℂ :=
  ∑' n : ℤ, scalarAmplitude a u ((n : ℝ) / L)

theorem scalarAmplitude_hasCompactSupport (a u : ℝ) :
    HasCompactSupport (scalarAmplitude a u) := by
  have hc : HasCompactSupport Fourier.chi0Complex :=
    Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero
  have ht : HasCompactSupport (fun x : ℝ => Fourier.chi0Complex (x - a)) := by
    simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hc.comp_homeomorph (Homeomorph.addRight (-a))
  exact ht.mul_right

@[fun_prop] theorem scalarAmplitude_contDiff (a u : ℝ) :
    ContDiff ℝ ∞ (scalarAmplitude a u) := by
  unfold scalarAmplitude
  simp only [Real.fourierChar_apply]
  apply ContDiff.mul
  · exact Fourier.chi0Complex_contDiff.comp (by fun_prop)
  · exact ((Complex.contDiff_exp : ContDiff ℂ ∞ Complex.exp).restrict_scalars ℝ).comp
      ((Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul (contDiff_const.mul contDiff_id))).mul contDiff_const)

/-- The compact modulation bundled for the landed Poisson theorem. -/
@[expose] noncomputable def scalarAmplitudeSchwartz (a u : ℝ) : 𝓢(ℝ, ℂ) :=
  (scalarAmplitude_hasCompactSupport a u).toSchwartzMap (scalarAmplitude_contDiff a u)

@[simp] theorem scalarAmplitudeSchwartz_apply (a u x : ℝ) :
    scalarAmplitudeSchwartz a u x = scalarAmplitude a u x := rfl

/-- The Fourier transform changes only its frequency and a unit translation phase. -/
theorem scalarAmplitude_fourier_norm (a u v : ℝ) :
    ‖𝓕 (scalarAmplitudeSchwartz a u) v‖ = ‖𝓕 Fourier.chi0Complex (u + v)‖ := by
  have hi : (∫ x : ℝ, Real.fourierChar (inner ℝ x (-(u + v))) •
      Fourier.chi0Complex (x - a)) = 𝓕 (scalarAmplitudeSchwartz a u) v := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul,
      scalarAmplitudeSchwartz_apply, scalarAmplitude]
    have he := congrArg (fun z : ℝ => (Real.fourierChar z : ℂ))
      (show x * -(u + v) = -(x * v) + -u * x by ring)
    simp only [AddChar.map_add_eq_mul, Circle.coe_mul] at he
    rw [he]
    ring
  rw [← hi, Fourier.norm_oscillatory_translate_eq, neg_neg]

/-- The scalar Poisson identity on `L⁻¹ℤ`. -/
theorem scalarLatticeSum_poisson {L : ℝ} (hL : 0 < L) (a u : ℝ) :
    scalarLatticeSum L a u = (L : ℂ) *
      ∑' m : ℤ, 𝓕 (scalarAmplitudeSchwartz a u) (L * m) := by
  simpa only [scalarLatticeSum, scalarAmplitudeSchwartz_apply] using
    Fourier.poisson_scaled (scalarAmplitudeSchwartz a u) hL

/-- TARGET `lemlin`: the nonnegative Poisson majorant, with no convergence premise. -/
theorem enorm_scalarLatticeSum_le {L : ℝ} (hL : 0 < L) (a u : ℝ) :
    ENNReal.ofReal ‖scalarLatticeSum L a u‖ ≤ ENNReal.ofReal L *
      ∑' m : ℤ, ENNReal.ofReal ‖𝓕 Fourier.chi0Complex (u + L * m)‖ := by
  calc
    _ = ENNReal.ofReal L * ‖∑' m : ℤ, 𝓕 (scalarAmplitudeSchwartz a u) (L * m)‖ₑ := by
      rw [scalarLatticeSum_poisson hL, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hL.le, ENNReal.ofReal_mul hL.le, ofReal_norm]
    _ ≤ ENNReal.ofReal L * ∑' m : ℤ, ‖𝓕 (scalarAmplitudeSchwartz a u) (L * m)‖ₑ :=
      mul_le_mul_right enorm_tsum_le_tsum_enorm _
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      rw [← ofReal_norm, scalarAmplitude_fourier_norm]

end WaveTurbulence.LemLin

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.AffineFourier
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The nonnegative envelope for the cubic integral

After integrating in `x`, both choices of the source quadratic phase have
the same absolute majorant. Its two frequency slopes give the two stationary
phase bounds without differentiating a parameter-dependent amplitude.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory
open scoped FourierTransform

/-- The common two-variable nonnegative Fourier envelope. -/
@[expose] noncomputable def scalarEnvelope (f g h : ScalarCutoff) (A B C : ℝ) : ℝ :=
  ∫ z : ℝ, ∫ y : ℝ, ‖g y‖ * ‖h z‖ * ‖𝓕 f.schwartz (A + B * y + C * z)‖

theorem scalarEnvelope_nonneg (f g h : ScalarCutoff) (A B C : ℝ) :
    0 ≤ scalarEnvelope f g h A B C :=
  integral_nonneg (fun z => integral_nonneg (fun y => by positivity))

/-- The envelope is integrable before any nonzero-slope assumption. -/
theorem integrable_scalarEnvelope (f g h : ScalarCutoff) (A B C : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      ‖g p.1‖ * ‖h p.2‖ * ‖𝓕 f.schwartz (A + B * p.1 + C * p.2)‖) := by
  have hg := g.integrable.norm.mul_prod h.integrable.norm
  have hmajor := hg.mul_const (SchwartzMap.seminorm ℂ 0 0 (𝓕 f.schwartz))
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (g.smooth.continuous.comp continuous_fst).norm.mul
        (h.smooth.continuous.comp continuous_snd).norm
    · exact ((𝓕 f.schwartz).continuous.comp (by fun_prop)).norm
  · apply ae_of_all
    intro p
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ (𝓕 f.schwartz) _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Exchanging the two free variables exchanges their slopes. -/
theorem scalarEnvelope_swap (f g h : ScalarCutoff) (A B C : ℝ) :
    scalarEnvelope f g h A B C = scalarEnvelope f h g A C B := by
  unfold scalarEnvelope
  rw [← integral_integral_swap (integrable_scalarEnvelope f g h A B C)]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [show A + B * y + C * z = A + C * z + B * y by ring]
  ring

/-- One nonzero slope supplies the reciprocal-parameter gain. -/
theorem scalarEnvelope_le_slope (f g h : ScalarCutoff) (A C : ℝ) {B : ℝ} (hB : B ≠ 0) :
    scalarEnvelope f g h A B C ≤
      (∫ z : ℝ, ‖h z‖) * SchwartzMap.seminorm ℂ 0 0 g.schwartz *
        (|B|⁻¹ * ∫ u : ℝ, ‖𝓕 f.schwartz u‖) := by
  have hi := h.integrable.norm.mul_const
    (SchwartzMap.seminorm ℂ 0 0 g.schwartz * (|B|⁻¹ * ∫ u : ℝ, ‖𝓕 f.schwartz u‖))
  have hbound : ∀ᵐ z : ℝ,
      (∫ y : ℝ, ‖g y‖ * ‖h z‖ * ‖𝓕 f.schwartz (A + B * y + C * z)‖) ≤
        ‖h z‖ * (SchwartzMap.seminorm ℂ 0 0 g.schwartz *
          (|B|⁻¹ * ∫ u : ℝ, ‖𝓕 f.schwartz u‖)) := by
    apply ae_of_all
    intro z
    have hb := integral_cutoff_fourier_affine_le f g hB (A + C * z)
    have he : (∫ y : ℝ, ‖g y‖ * ‖h z‖ * ‖𝓕 f.schwartz (A + B * y + C * z)‖) =
        ‖h z‖ * ∫ y : ℝ, ‖g y‖ * ‖𝓕 f.schwartz ((A + C * z) + B * y)‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro y
      dsimp only
      rw [show A + B * y + C * z = (A + C * z) + B * y by ring]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  unfold scalarEnvelope
  calc
    _ ≤ ∫ z : ℝ, ‖h z‖ * (SchwartzMap.seminorm ℂ 0 0 g.schwartz *
        (|B|⁻¹ * ∫ u : ℝ, ‖𝓕 f.schwartz u‖)) :=
      integral_mono_of_nonneg
        (ae_of_all _ (fun z => integral_nonneg (fun y => by positivity))) hi hbound
    _ = _ := by
      rw [integral_mul_const]
      ring

/-- The envelope also has a uniform bound without a nonzero slope. -/
theorem scalarEnvelope_le_mass (f g h : ScalarCutoff) (A B C : ℝ) :
    scalarEnvelope f g h A B C ≤
      (∫ x : ℝ, ‖f x‖) * (∫ y : ℝ, ‖g y‖) * ∫ z : ℝ, ‖h z‖ := by
  let M : ℝ := ∫ x : ℝ, ‖f x‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  have hgM : 0 ≤ ∫ y : ℝ, ‖g y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hinner (z : ℝ) :
      (∫ y : ℝ, ‖g y‖ * ‖h z‖ * ‖𝓕 f.schwartz (A + B * y + C * z)‖) ≤
        (M * ∫ y : ℝ, ‖g y‖) * ‖h z‖ := by
    have hbound (y : ℝ) : ‖g y‖ * ‖h z‖ * ‖𝓕 f.schwartz (A + B * y + C * z)‖ ≤
        ‖g y‖ * (M * ‖h z‖) := by
      have hf := Real.norm_fourier_le_integral_norm (f : ℝ → ℂ) (A + B * y + C * z)
      calc
        _ ≤ ‖g y‖ * ‖h z‖ * M := mul_le_mul_of_nonneg_left hf (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∫ y : ℝ, ‖g y‖ * (M * ‖h z‖) := integral_mono_of_nonneg
        (ae_of_all _ (fun _ => by positivity)) (g.integrable.norm.mul_const _) (ae_of_all _ hbound)
      _ = _ := by rw [integral_mul_const]; ring
  unfold scalarEnvelope
  calc
    _ ≤ ∫ z : ℝ, (M * ∫ y : ℝ, ‖g y‖) * ‖h z‖ := integral_mono_of_nonneg
      (ae_of_all _ (fun z => integral_nonneg (fun y => by positivity)))
      (h.integrable.norm.const_mul _) (ae_of_all _ hinner)
    _ = _ := by rw [integral_const_mul]

end WaveTurbulence.LemLin

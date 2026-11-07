/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.TripleFrequencySymmetries

/-!
# Scalar sum-frequency pairing symmetries

The one-exit source phase has a minus sign in the first frequency.
Reflection removes it, and coordinate exchanges place the weak bracket
denominator in the first coordinate without altering the sum phase.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
namespace WaveTurbulence.SumintPar

/-- First-frequency reflection removes the source sign from a scalar sum-frequency pairing. -/
theorem lintegral_native_one_exit_reflect (a b c : ℝ) (H : ℝ → ℝ≥0∞) :
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 1+ξ 2-ξ 0)) =
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 0+ξ 1+ξ 2)) := by
  let f (ξ : Fin 3 → ℝ) := scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
    scalarPowerKernel c (ξ 2)*H (ξ 0+ξ 1+ξ 2)
  have he := volume_preserving_frequencyReflectFirst.lintegral_comp_emb frequencyReflectFirst.measurableEmbedding f
  calc
    _ = ∫⁻ ξ, f (frequencyReflectFirst ξ) := by
      apply lintegral_congr
      intro ξ
      change _ = scalarPowerKernel a (-ξ 0)*scalarPowerKernel b (ξ 1)*scalarPowerKernel c (ξ 2)*H (-ξ 0+ξ 1+ξ 2)
      rw [scalarPowerKernel_neg,show -ξ 0+ξ 1+ξ 2 = ξ 1+ξ 2-ξ 0 by ring]
    _ = _ := he

/-- Exchanging the first two frequencies preserves the scalar sum-frequency pairing. -/
theorem lintegral_native_one_exit_swap_one (a b c : ℝ) (H : ℝ → ℝ≥0∞) :
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 0+ξ 1+ξ 2)) =
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel b (ξ 0)*scalarPowerKernel a (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 0+ξ 1+ξ 2)) := by
  let f (ξ : Fin 3 → ℝ) := scalarPowerKernel b (ξ 0)*scalarPowerKernel a (ξ 1)*
    scalarPowerKernel c (ξ 2)*H (ξ 0+ξ 1+ξ 2)
  have he := (volume_preserving_frequencySwapFirst 1).lintegral_comp_emb (frequencySwapFirst 1).measurableEmbedding f
  calc
    _ = ∫⁻ ξ, f (frequencySwapFirst 1 ξ) := by
      apply lintegral_congr
      intro ξ
      rw [frequencySwapFirst_one_apply]
      change _ = scalarPowerKernel b (ξ 1)*scalarPowerKernel a (ξ 0)*scalarPowerKernel c (ξ 2)*H (ξ 1+ξ 0+ξ 2)
      rw [add_comm (ξ 1) (ξ 0)]
      ring
    _ = _ := he

/-- Exchanging the first and third frequencies preserves the scalar sum-frequency pairing. -/
theorem lintegral_native_one_exit_swap_two (a b c : ℝ) (H : ℝ → ℝ≥0∞) :
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 0+ξ 1+ξ 2)) =
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel c (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel a (ξ 2)*H (ξ 0+ξ 1+ξ 2)) := by
  let f (ξ : Fin 3 → ℝ) := scalarPowerKernel c (ξ 0)*scalarPowerKernel b (ξ 1)*
    scalarPowerKernel a (ξ 2)*H (ξ 0+ξ 1+ξ 2)
  have he := (volume_preserving_frequencySwapFirst 2).lintegral_comp_emb (frequencySwapFirst 2).measurableEmbedding f
  calc
    _ = ∫⁻ ξ, f (frequencySwapFirst 2 ξ) := by
      apply lintegral_congr
      intro ξ
      rw [frequencySwapFirst_two_apply]
      change _ = scalarPowerKernel c (ξ 2)*scalarPowerKernel b (ξ 1)*scalarPowerKernel a (ξ 0)*H (ξ 2+ξ 1+ξ 0)
      rw [show ξ 2+ξ 1+ξ 0 = ξ 0+ξ 1+ξ 2 by ring]
      ring
    _ = _ := he

end WaveTurbulence.SumintPar

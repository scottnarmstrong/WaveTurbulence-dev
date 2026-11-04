/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CellFourierBounds
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Finite products of the exact localized weight Fourier expansions

The expansion is taken before composing with the affine momentum maps.
This avoids dimension-dependent derivative losses from differentiating
those maps. The coefficient mass is a product of one-weight masses.
-/

public section

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.Sumint

/-- The literal modulation expansion of a finite product of localized source weights. -/
theorem finite_localizedWeight_expansion {ι : Type*} [Fintype ι] {d N : ℕ}
    (hN : N ≠ 0) (hdN : d + 1 ≤ N) (K : ι → ℕ) (F : ι → Mom d → ℂ)
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hF : ∀ i, SNorm N (K i) (F i) ≤ ENNReal.ofReal (B i))
    (a : ι → Fin d → ℤ) (p : ι → Mom d) :
    (∫ ξ : ι → Mom d, ∏ i, (Real.fourierChar (inner ℝ (ξ i) (p i)) : ℂ) *
      𝓕 (localizedWeight (a i) (F i)) (ξ i)) =
        ∏ i, localizedWeight (a i) (F i) (p i) := by
  calc
    _ = ∏ i : ι, ∫ ξ : Mom d, (Real.fourierChar (inner ℝ ξ (p i)) : ℂ) *
        𝓕 (localizedWeight (a i) (F i)) ξ :=
      integral_fintype_prod_volume_eq_prod (𝕜 := ℂ) (E := fun _ : ι => Mom d) _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact localizedWeight_fourier_expansion hN hdN (hB i) (hF i) (a i) (p i)

/-- The tensor Fourier coefficient has exactly the product of the individual L1 masses. -/
theorem integral_norm_tensor_fourier {ι : Type*} [Fintype ι] {d : ℕ}
    (F : ι → Mom d → ℂ) :
    (∫ ξ : ι → Mom d, ‖∏ i, 𝓕 (F i) (ξ i)‖) = ∏ i, ∫ ξ : Mom d, ‖𝓕 (F i) ξ‖ := by
  simp_rw [norm_prod]
  exact integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : ι => Mom d)
    (fun i ξ => ‖𝓕 (F i) ξ‖)

/-- The tensor coefficient mass has only an exponential-in-the-number-of-weights loss. -/
theorem integral_norm_tensor_localized_fourier_le {ι : Type*} [Fintype ι] {d N : ℕ}
    (hN : N ≠ 0) (hdN : d + 1 ≤ N) (K : ι → ℕ) (F : ι → Mom d → ℂ)
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hF : ∀ i, SNorm N (K i) (F i) ≤ ENNReal.ofReal (B i))
    (a : ι → Fin d → ℤ) :
    (∫ ξ : ι → Mom d, ‖∏ i, 𝓕 (localizedWeight (a i) (F i)) (ξ i)‖) ≤
      cellFourierFactor d ^ Fintype.card ι * ∏ i, B i := by
  rw [integral_norm_tensor_fourier]
  calc
    _ ≤ ∏ i, cellFourierFactor d * B i := by
      apply Finset.prod_le_prod₀ (fun i _ => integral_nonneg (fun _ => norm_nonneg _))
      intro i _
      exact (localizedWeight_fourier_integrable_and_bound hN hdN (hB i) (hF i) (a i)).2
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- The tensor Fourier coefficient is integrable, so later Fubini arguments have a genuine L1 input. -/
theorem integrable_tensor_localized_fourier {ι : Type*} [Fintype ι] {d N : ℕ}
    (hN : N ≠ 0) (hdN : d + 1 ≤ N) (K : ι → ℕ) (F : ι → Mom d → ℂ)
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hF : ∀ i, SNorm N (K i) (F i) ≤ ENNReal.ofReal (B i))
    (a : ι → Fin d → ℤ) :
    Integrable (fun ξ : ι → Mom d => ∏ i, 𝓕 (localizedWeight (a i) (F i)) (ξ i)) := by
  simpa only [volume_pi] using Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure (Mom d)))
    (fun i => (localizedWeight_fourier_integrable_and_bound hN hdN (hB i) (hF i) (a i)).1)

end WaveTurbulence.Sumint

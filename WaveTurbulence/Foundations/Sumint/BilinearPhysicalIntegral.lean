/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearFourier
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Exact identification with the landed bilinear phase integral

The Fourier transform of the flattened compact amplitude has exactly
the cutoff, measure, sign, and frequency shifts expected by `lemlayer1`.
-/

public section

open MeasureTheory WithLp

namespace WaveTurbulence.Sumint

/-- The physical integrand retains the literal landed tensor cutoffs. -/
theorem flatBilinearAmplitude_pair_eq {d : ℕ} (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) (p : Mom d × Mom d) :
    flatBilinearAmplitude c s ξ ζ (pairFlatten d p) =
      Real.fourierChar (inner ℝ p.1 ξ + inner ℝ p.2 ζ + s * inner ℝ p.1 p.2) •
        (Fourier.chi0MomSchwartz d (p.1 - toLp 2 (c 0)) *
          Fourier.chi0MomSchwartz d (p.2 - toLp 2 (c 1))) := by
  simp only [flatBilinearAmplitude, pair_cutoff_eq, flatMomentum_pairFlatten_zero,
    flatMomentum_pairFlatten_one, Fourier.chi0MomSchwartz_apply, Circle.smul_def,
    smul_eq_mul, Real.fourierChar_apply]
  have h₀ : ofLp (p.1 - toLp 2 (c 0)) = ofLp p.1 - c 0 := rfl
  have h₁ : ofLp (p.2 - toLp 2 (c 1)) = ofLp p.2 - c 1 := rfl
  rw [h₀, h₁, mul_comm]

/-- Fubini turns the joint compact integral into the landed iterated bilinear phase integral. -/
theorem integral_flatBilinearAmplitude_pair {d : ℕ} (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) :
    (∫ p : Mom d × Mom d, flatBilinearAmplitude c s ξ ζ (pairFlatten d p)) =
      Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
        (toLp 2 (c 0)) (toLp 2 (c 1)) ξ ζ s := by
  have hc : Continuous (fun p : Mom d × Mom d =>
      flatBilinearAmplitude c s ξ ζ (pairFlatten d p)) :=
    (flatBilinearAmplitude_contDiff c s ξ ζ).continuous.comp (pairFlatten d).continuous
  have hi : Integrable (fun p : Mom d × Mom d =>
      flatBilinearAmplitude c s ξ ζ (pairFlatten d p)) := hc.integrable_of_hasCompactSupport
    ((flatBilinearAmplitude_hasCompactSupport c s ξ ζ).comp_homeomorph
      (pairFlatten d).toHomeomorph)
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  unfold Fourier.bilinearPhaseIntegral
  apply integral_congr_ae
  apply ae_of_all
  intro y
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact flatBilinearAmplitude_pair_eq c s ξ ζ (x, y)

/-- The exact Fourier-side object to which the landed stationary-phase lattice bound applies. -/
theorem timeFourier_flatBilinearAmplitude_eq_phaseIntegral {d : ℕ}
    (c : Fin 2 → Fin d → ℝ) (s : ℝ) (ξ ζ : Mom d) (ν : Fin (2*d) → ℝ) :
    Fourier.timeFourier (flatBilinearAmplitude c s ξ ζ) ν =
      Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
        (toLp 2 (c 0)) (toLp 2 (c 1)) (ξ - flatMomentum 0 ν) (ζ - flatMomentum 1 ν) s := by
  rw [timeFourier_flatBilinearAmplitude, integral_flatBilinearAmplitude_pair]

end WaveTurbulence.Sumint

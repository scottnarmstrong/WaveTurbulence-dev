/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeEuclidean

/-! # Exact spatial Fourier modulation with the source positive character -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped FourierTransform
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A positive source modulation translates the Fourier argument by minus
its actual frequency. This identity needs no integrability premise. -/
theorem fourier_positive_modulation (f : V → ℂ) (β ξ : V) :
    𝓕 (fun x => Real.fourierChar (inner ℝ β x) • f x) ξ = 𝓕 f (ξ-β) := by
  simp only [Real.fourier_eq]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change Real.fourierChar (-inner ℝ x ξ) • (Real.fourierChar (inner ℝ β x) • f x) =
      Real.fourierChar (-inner ℝ x (ξ-β)) • f x
    have hp : -inner ℝ x ξ+inner ℝ β x = -inner ℝ x (ξ-β) := by
      rw [inner_sub_right,real_inner_comm β x]
      ring
    rw [smul_smul,← AddChar.map_add_eq_mul,hp])

end WaveTurbulence.RegAsymp

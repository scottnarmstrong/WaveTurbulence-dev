/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductMixture
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability

/-! Ported by source from C2-B-TOP `Cut2BReg.PointwiseProduct` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Pointwise Fubini for the common Fourier-measure source extensions -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

/-- Conditional Fubini helper. Its bound is physical pointwise control, not the target norm. -/
theorem integral_product_amplitude_kernel {U V α : Type*}
    [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace α]
    (μ : Measure U) [SFinite μ] (F : SpatialMeasure V α) (A : U → ℂ) (hiA : Integrable A μ)
    (K : U × α → ℂ) (hK : AEStronglyMeasurable K (μ.prod F.μ))
    {H : ℝ≥0∞} (hH : H < ⊤) (hb : ∀ u, ‖K u‖ₑ ≤ H) :
    (∫ u, F.amplitude u.2 * A u.1 * K u ∂μ.prod F.μ) =
      ∫ a, F.amplitude a * (∫ u, A u * K (u, a) ∂μ) ∂F.μ := by
  have hi := integrable_mul_of_uniform_enorm_bound (μ.prod F.μ)
    (fun u : U × α => A u.1 * F.amplitude u.2) K (hiA.mul_prod F.amplitude_integrable) hK hH hb
  have he := integral_prod_symm (fun u : U × α => A u.1 * F.amplitude u.2 * K u) hi
  calc
    _ = ∫ u, A u.1 * F.amplitude u.2 * K u ∂μ.prod F.μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _ = _ := by
      rw [he]
      apply integral_congr_ae
      apply ae_of_all
      intro a
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)

end WaveTurbulence.Flower.IncTop
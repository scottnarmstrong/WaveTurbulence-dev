/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierLpPairing
public import WaveTurbulence.Foundations.Fourier.LpDuality
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
import Mathlib.Tactic

/-!
# Hausdorff–Young with constant one

TARGET L2370. The ordinary Fourier integral sends `L¹ ∩ Lᵖ` to `L^{p'}`
with norm at most one for `1 ≤ p ≤ 2`, including the `L∞` endpoint.
Integrability is the typing condition for the ordinary integral transform;
in particular the theorem applies to the proof's compactly supported input.
The coordinate version applies directly to the paper's two time variables.
-/

public section

open MeasureTheory WithLp
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- TARGET L2370: Hausdorff–Young for finite conjugate exponents, with constant one. -/
theorem integral_fourier_hausdorffYoung {p q : ℝ} (hpq : p.HolderConjugate q)
    (hp2 : p ≤ 2) {f : V → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    eLpNorm (𝓕 f) (ENNReal.ofReal q) ≤ eLpNorm f (ENNReal.ofReal p) := by
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (L := innerₗ V) continuous_inner hf
  have h := eLpNorm_le_of_pairing hpq hc.measurable
    (Real.norm_fourier_le_integral_norm f)
    (lpNorm_nonneg (f := f) (p := ENNReal.ofReal p) (μ := volume))
    (fun g hg hgp => fourier_pairing_Lp hpq.lt.le hp2 hf hg hfp hgp)
  simpa only [ofReal_lpNorm hfp] using h

/-- TARGET L2370: the full closed exponent interval, including `p = 1`,
for the ordinary Fourier integral. The Fourier normalization gives constant one. -/
theorem integral_fourier_hausdorffYoung_conj {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {f : V → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    eLpNorm (𝓕 f) (ENNReal.conjExponent (ENNReal.ofReal p)) ≤ eLpNorm f (ENNReal.ofReal p) := by
  rcases eq_or_lt_of_le hp1 with hp | hp
  · subst p
    simpa [ENNReal.conjExponent] using integral_fourier_eLpNorm_top_le hf
  · have hpq := Real.HolderConjugate.conjExponent hp
    let : ENNReal.HolderConjugate (ENNReal.ofReal p)
        (ENNReal.ofReal (Real.conjExponent p)) := hpq.ennrealOfReal
    rw [ENNReal.HolderConjugate.conjExponent_eq (p := ENNReal.ofReal p)
      (q := ENNReal.ofReal (Real.conjExponent p))]
    exact integral_fourier_hausdorffYoung hpq hp2 hf hfp

/-- Hausdorff–Young in the product-coordinate convention used by `𝔛` norms.
Taking `r = 2` is exactly TARGET L2370. -/
theorem timeFourier_hausdorffYoung {r : ℕ} {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {f : (Fin r → ℝ) → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    eLpNorm (timeFourier f) (ENNReal.conjExponent (ENNReal.ofReal p)) ≤
      eLpNorm f (ENNReal.ofReal p) := by
  let fE := fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)
  have hp := PiLp.volume_preserving_ofLp (Fin r)
  have hfe : Integrable fE := memLp_one_iff_integrable.mp
    ((memLp_one_iff_integrable.mpr hf).comp_measurePreserving hp)
  have hfpe : MemLp fE (ENNReal.ofReal p) := hfp.comp_measurePreserving hp
  have he : (fun ξ : EuclideanSpace ℝ (Fin r) => timeFourier f (ofLp ξ)) = 𝓕 fE := by
    funext ξ
    simpa only [toLp_ofLp] using timeFourier_eq_euclidean f (ofLp ξ)
  have hl : eLpNorm (𝓕 fE) (ENNReal.conjExponent (ENNReal.ofReal p)) =
      eLpNorm (timeFourier f) (ENNReal.conjExponent (ENNReal.ofReal p)) := by
    rw [← he]
    exact eLpNorm_comp_measurePreserving (timeFourier_continuous hf).aestronglyMeasurable hp
  have hr : eLpNorm fE (ENNReal.ofReal p) = eLpNorm f (ENNReal.ofReal p) :=
    eLpNorm_comp_measurePreserving hfp.aestronglyMeasurable hp
  rw [← hl, ← hr]
  exact integral_fourier_hausdorffYoung_conj hp1 hp2 hfe hfpe

end WaveTurbulence.Fourier

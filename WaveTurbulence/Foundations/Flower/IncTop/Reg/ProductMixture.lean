/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.FrequencyTranslation
public import WaveTurbulence.Foundations.Incoh.SpectralSpatialMixture
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootAmplitudeMixture

/-! Ported by source from C2-B-TOP `Cut2BReg.ProductMixture` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Full spatial norm transport on a product Fourier measure

The Fourier parameter is integrated together with the source spectral
variables. Root derivatives therefore fall only on the source amplitude.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

/-- A root-independent scalar multiplies every actual amplitude jet by that scalar. -/
theorem iteratedFDeriv_mul_amplitude {d j : ℕ} (A : Mom d → ℂ) (c : ℂ)
    (hA : ContDiff ℝ j A) (k : Mom d) :
    iteratedFDeriv ℝ j (fun k => c * A k) k = c • iteratedFDeriv ℝ j A k :=
  by simpa only [smul_eq_mul] using (iteratedFDeriv_const_smul_apply' (a := c) hA.contDiffAt)

end WaveTurbulence.Flower.IncTop
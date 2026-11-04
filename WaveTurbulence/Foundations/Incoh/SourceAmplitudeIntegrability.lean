/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceLinkKernelIdentity
public import WaveTurbulence.Foundations.Incoh.SpectralLinkContinuity

/-!
# Integrability of the actual source spectral amplitude

The root modulation and garden phase have unit modulus. The actual
Fourier coefficient therefore has the previously proved common envelope.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual amplitude is a source density at zero free link momenta. -/
theorem MomentumTreeData.sourceSpectralAmplitude_eq_density_zero {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    P.sourceSpectralAmplitude ζ f c z k ξ =
      P.localizedSourceSpectralDensity ζ f c z k (fun _ _ => 0) ξ := by
  rw [P.localizedSourceSpectralDensity_eq_root_link_phase]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one,
    Finset.prod_const_one, mul_one, sourceSpectralAmplitude]

/-- The actual source amplitude has the same parameter-independent pointwise envelope. -/
theorem MomentumTreeData.enorm_sourceSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ‖P.sourceSpectralAmplitude ζ f c z k ξ‖ₑ =
      ‖localizedSpectralReference (n := n) f c ξ‖ₑ := by
  rw [P.sourceSpectralAmplitude_eq_density_zero]
  exact P.enorm_localizedSourceSpectralDensity ζ f c z k (fun _ _ => 0) ξ

/-- Actual source spatial bounds give spectral amplitude integrability at every root momentum. -/
theorem MomentumTreeData.integrable_sourceSpectralAmplitude {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Integrable (P.sourceSpectralAmplitude ζ f c z k) := by
  have he : P.sourceSpectralAmplitude ζ f c z k =
      P.localizedSourceSpectralDensity ζ f c z k (fun _ _ => 0) := by
    funext ξ
    exact P.sourceSpectralAmplitude_eq_density_zero ζ f c z k ξ
  rw [he]
  exact P.integrable_localizedSourceSpectralDensity ζ f c z hK hB h k (fun _ _ => 0)

/-- The actual Fourier coefficient and computed root phase give a continuous spectral amplitude. -/
theorem MomentumTreeData.continuous_sourceSpectralAmplitude {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Continuous (P.sourceSpectralAmplitude ζ f c z k) := by
  have hc : Continuous (localizedSpectralCoefficient f c z) := by
    unfold localizedSpectralCoefficient
    apply continuous_finsetProd
    intro i _
    exact (Fourier.timeFourier_continuous (Fourier.integrable_of_timeFourierNorm_lt_top
      (timeFourierNorm_localizedCellProfiles_lt_top f c z hK hB h i))).comp (continuous_apply i)
  unfold sourceSpectralAmplitude
  fun_prop

end WaveTurbulence.Incoh

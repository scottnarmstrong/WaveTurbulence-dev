/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralIdentity

/-!
# A common pointwise spectral envelope

The actual signed density has an amplitude independent of every momentum
parameter and every link-cell center. Center dependence is a unit phase,
which permits a momentum supremum before spectral integration.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual reference Fourier density: all link centers are set to zero. -/
@[expose] def localizedSpectralReference {d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  ∏ i, Fourier.timeFourier (localizedCellProfiles f c (fun _ => 0) i) (ξ i)

/-- Pointwise equality of amplitudes, stronger than a parameter-uniform inequality. -/
theorem MomentumTreeData.enorm_localizedSourceSpectralDensity {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ‖P.localizedSourceSpectralDensity ζ f c z k x ξ‖ₑ =
      ‖localizedSpectralReference (n := n) f c ξ‖ₑ := by
  have hζ : ‖(ζ : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
  simp only [localizedSourceSpectralDensity, enorm_mul, hζ, one_mul,
    cellProductFourierIntegrand, localizedSpectralReference]
  rw [← ofReal_norm, ← ofReal_norm]
  congr 1
  simp only [norm_prod, Circle.norm_smul]
  apply Finset.prod_congr rfl
  intro i _
  cases i with
  | inl a => rfl
  | inr p =>
      simpa only [toReal_enorm, localizedCellProfiles] using congrArg ENNReal.toReal
        (enorm_timeFourier_halfLinkCell_eq (z p) (ξ (.inr p)))

/-- The common reference density is integrable, directly from source spatial norms. -/
theorem integrable_localizedSpectralReference {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    Integrable (localizedSpectralReference (n := n) f c) := by
  change Integrable (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
    ∏ i, Fourier.timeFourier (localizedCellProfiles f c (fun _ => 0) i) (ξ i))
    (Measure.pi (fun _ : LocalizedCellIndex n m => (volume : Measure (Fin d → ℝ))))
  apply Integrable.fintype_prod (f := fun i ξ =>
    Fourier.timeFourier (localizedCellProfiles f c (fun _ => 0) i) ξ)
  intro i
  exact Fourier.integrable_timeFourier_of_norm_lt_top (le_refl (0 : ℝ))
    (timeFourierNorm_localizedCellProfiles_lt_top f c (fun _ => 0) hK hB h i)

end WaveTurbulence.Incoh

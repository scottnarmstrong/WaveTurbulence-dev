/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedCellProfiles
public import WaveTurbulence.Foundations.Incoh.SignedLeafDecomposition

/-!
# Exact signed spectral identity for the localized source momentum weight

TARGET (incohproof6–9). Both the original input functions and the half-width
link cells use their actual Fourier transforms. The global garden sign is
retained in the density, whose integrability follows from source premises.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual signed joint Fourier density of one localized source term. -/
@[expose] def MomentumTreeData.localizedSourceSpectralDensity {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  (ζ : ℂ) * cellProductFourierIntegrand (localizedCellProfiles f c z)
    (P.localizedCellMomenta k x) ξ

/-- The actual signed localized source term is its literal joint Fourier integral. -/
theorem MomentumTreeData.signed_localizedLeafWeight_eq_spectralIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    (ζ : ℂ) * P.localizedLeafWeight f c k x * halfCellArrayWeight z (fun p => x p.1 p.2) =
      ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        P.localizedSourceSpectralDensity ζ f c z k x ξ := by
  have hp := prod_eq_cellProductFourierIntegral (localizedCellProfiles f c z)
    (continuous_localizedCellProfiles f c z ((Nat.zero_lt_succ d).trans_le hK) h)
    (timeFourierNorm_localizedCellProfiles_lt_top f c z hK hB h)
    (P.localizedCellMomenta k x)
  rw [P.prod_localizedCellProfiles f c z k x] at hp
  simpa only [localizedSourceSpectralDensity, integral_const_mul, mul_assoc] using
    congrArg ((ζ : ℂ) * ·) hp

/-- The actual signed density is integrable at every source momentum. -/
theorem MomentumTreeData.integrable_localizedSourceSpectralDensity {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    Integrable (P.localizedSourceSpectralDensity ζ f c z k x) :=
  (integrable_cellProductFourierIntegrand (localizedCellProfiles f c z)
    (timeFourierNorm_localizedCellProfiles_lt_top f c z hK hB h)
    (P.localizedCellMomenta k x)).const_mul (ζ : ℂ)

end WaveTurbulence.Incoh

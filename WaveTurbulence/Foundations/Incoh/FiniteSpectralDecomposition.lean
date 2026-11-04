/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralMassBound

/-!
# Finite exact spectral decomposition of the signed source input weight

TARGET (incohproof8–9). Every localized source weight is an exponentially
bounded finite sum of literal, integrable spectral densities. The finite
index set depends only on structural data and localization centers.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Exact source decomposition with finite profile integrals and the literal global sign. -/
theorem exists_finite_spectral_decomposition (d : ℕ) (hd : 0 < d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n m w : ℕ, ∀ P : MomentumTreeData n m w,
      ∀ k : Mom d, ∀ c : Fin m → Fin d → ℤ,
      ∃ S : Finset ((Fin n × Fin 2) → Fin d → ℤ), (S.card : ℝ) ≤ C₀ ^ n ∧
        ∀ K M : ℕ, ∀ B : ℝ, d + 1 ≤ K → 0 ≤ B →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ ζ : Circle, ∀ x : Fin n → Fin 2 → Mom d,
          (ζ : ℂ) * P.localizedLeafWeight f c k x =
            ∑ z ∈ S, ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
              P.localizedSourceSpectralDensity ζ f c z k x ξ := by
  obtain ⟨C₀, hC₀, h⟩ := exists_signedLeafWeight_decomposition d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro n m w P k c
  obtain ⟨S, hcard, hS⟩ := h n m w P k c
  refine ⟨S, hcard, ?_⟩
  intro K M B hK hB f hf ζ x
  rw [hS ζ f x]
  apply Finset.sum_congr rfl
  intro z _
  exact P.signed_localizedLeafWeight_eq_spectralIntegral ζ f c z hK hB hf k x

end WaveTurbulence.Incoh

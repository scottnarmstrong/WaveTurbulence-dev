/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralLinkIntegral
public import WaveTurbulence.Foundations.Incoh.LocalizedSourceIntegral

/-!
# Exact source identity with the proved analytic link kernels

TARGET (incohproof8–10). The normalized actual localized source operator
is a spectral mixture of literal normalized link-product integrals.
The amplitude, centers and shifts are computed from the source inputs.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual spectral amplitude, retaining the garden sign and root modulation. -/
@[expose] def MomentumTreeData.sourceSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  (ζ : ℂ) * (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ) *
    localizedSpectralCoefficient f c z ξ

/-- TARGET (incohproof8–10), as an equality for the literal source operator. -/
theorem MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixture {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    P.localizedSourceIntegral ζ L γ δ Q I f c z k =
      ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        P.sourceSpectralAmplitude ζ f c z k ξ *
          normalizedLinkIntegral L γ δ (P.spectralLinks Q z ξ) I := by
  rw [P.localizedSourceIntegral_eq_spectralIntegral ζ L γ δ Q I hI f c z hL hK hB h k,
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  have hs : (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ((∫ t in I, sourceTemporalPhase L γ δ Q p t) *
        linkArrayCutoff z (latticeMomentumArray L p)) *
        P.localizedSourceSpectralDensity ζ f c z k (fun i j => latticePoint L (p (i, j))) ξ) =
      P.sourceSpectralAmplitude ζ f c z k ξ *
        ∫ t in I, ∏ i, linkTimeFactor L γ δ (P.spectralLinks Q z ξ i) (t i) := by
    rw [← P.spectral_link_integral_eq L γ δ Q hL z ξ I hI, ← tsum_mul_left]
    apply tsum_congr
    intro p
    rw [P.localizedSourceSpectralDensity_eq_root_link_phase ζ f c z k
      (fun i j => latticePoint L (p (i, j))) ξ]
    unfold sourceSpectralAmplitude
    ring
  rw [hs]
  unfold normalizedLinkIntegral
  ring

end WaveTurbulence.Incoh

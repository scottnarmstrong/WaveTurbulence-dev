/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralLinkIntegral
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.LocalizedSourceIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceLinkKernelIdentity` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Exact source identity with the proved analytic link kernels

TARGET (incohproof8–10). The normalized actual localized source operator
is a spectral mixture of literal normalized link-product integrals.
The amplitude, centers and shifts are computed from the source inputs.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual spectral amplitude, retaining the garden sign and root modulation. -/
@[expose] def MomentumTreeData.sourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  (ζ : ℂ) * (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ) *
    localizedSpectralCoefficient f c z ξ

open WaveTurbulence.Incoh.MomentumTreeData in
/-- TARGET (incohproof8–10), as an equality for the literal source operator. -/
theorem MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f c z k =
      ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ *
          normalizedLinkIntegral L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I := by
  rw [(MomentumTreeData.localizedSourceIntegral_eq_spectralIntegralSpatial (P := P)) ζ L γ δ Q I hI f c z hL hK hB h k,
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  have hs : (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ((∫ t in I, sourceTemporalPhaseSpatial L γ δ Q p t) *
        linkArrayCutoff z (latticeMomentumArray L p)) *
        P.localizedSourceSpectralDensity ζ f c z k (fun i j => latticePoint L (p (i, j))) ξ) =
      (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ *
        ∫ t in I, ∏ i, linkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ i) (t i) := by
    rw [← (MomentumTreeData.spectral_link_integral_eqSpatial (P := P)) L γ δ Q hL z ξ I hI, ← tsum_mul_left]
    apply tsum_congr
    intro p
    rw [P.localizedSourceSpectralDensity_eq_root_link_phase ζ f c z k
      (fun i j => latticePoint L (p (i, j))) ξ]
    unfold sourceSpectralAmplitudeSpatial
    ring
  rw [hs]
  unfold normalizedLinkIntegral
  ring

end WaveTurbulence.Flower.IncTop
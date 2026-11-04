/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceAmplitudeIntegrability
public import WaveTurbulence.Foundations.Incoh.CoupleExtensionAgreement

/-!
# A canonical extension of the actual localized source couple

The extension is the actual spectral mixture of the proved scalar link
extensions. It agrees with the original normalized source lattice/time
operator with the two genuine external root constraints.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Canonical spectral extension of one actual leaf/link-localized source couple. -/
@[expose] def MomentumTreeData.sourceCoupleExtension {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ, P.sourceSpectralAmplitude ζ f c z k ξ *
    R.coupleExtension rootCutoff L γ δ (P.spectralLinks Q z ξ) I t

/-- Exact source agreement for the actual extension on the source external root box. -/
theorem MomentumTreeData.sourceCoupleExtension_agrees {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (t : Fin 2 → ℝ) (ht : t ∈ R.rootBox Q) (k : Mom d) :
    P.sourceCoupleExtension ζ R L γ δ Q I f c z t k =
      P.localizedSourceIntegral ζ L γ δ Q (I ∩ R.rootCut t) f c z k := by
  rw [P.localizedSourceIntegral_eq_linkKernelMixture ζ L γ δ Q (I ∩ R.rootCut t)
    (Set.inter_subset_left.trans hbox) f c z hL hK hB h k]
  unfold sourceCoupleExtension
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  congr 1
  exact R.coupleExtension_agrees hL γ δ (P.spectralLinks Q z ξ) hI hbox ht

end WaveTurbulence.Incoh

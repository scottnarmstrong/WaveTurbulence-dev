/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellMaskedCoupleDecay
public import WaveTurbulence.Foundations.Incoh.CouplePointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Pointwise countable recovery for the actual masked source extension -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Conditional pointwise Fubini typing from the independently proved root-marginal bound. -/
theorem MomentumTreeData.integrable_allCellMaskedCoupleSlice_of_uniformRootL1 {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : Fourier.CutoffControl χ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N)
    (τ t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => P.allCellMaskedSpectralAmplitude ζ f S k u *
      P.allCellCutoffCoupleKernel χ R L γ δ Q I S (t + τ) u) (sourceCellMeasure S) := by
  have hKs : StronglyMeasurable (P.allCellCutoffCoupleKernel χ R L γ δ Q I S (t + τ)) :=
    (P.stronglyMeasurable_allCellCutoffCoupleKernel hχ.continuous.measurable R hL γ δ Q I hI S).comp_measurable
      (g := fun u => (t + τ, u)) (measurable_const.prodMk measurable_id)
  apply integrable_mul_of_uniform_enorm_bound (sourceCellMeasure S)
    (P.allCellMaskedSpectralAmplitude ζ f S k) (P.allCellCutoffCoupleKernel χ R L γ δ Q I S (t + τ))
    (P.integrable_allCellMaskedSpectralAmplitude ζ f S hS hK hM hB h k) hKs.aestronglyMeasurable
    (N := ENNReal.ofReal hc.bound ^ 4 * N) (ENNReal.mul_lt_top (by finiteness) hN)
  intro u
  exact (R.enorm_coupleExtension_le hχ hc hL γ δ (P.spectralLinks Q u.1.2.val u.2)
    hI hbox (t + τ)).trans (mul_le_mul' le_rfl (hb _ _))

/-- The actual masked extension is the sum of its individual cell spectral integrals at every
external time, including the source boundary. -/
theorem MomentumTreeData.allCellMaskedSourceCoupleExtension_eq_tsum {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : Fourier.CutoffControl χ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N)
    (τ t : Fin 2 → ℝ) (k : Mom d) :
    P.allCellMaskedSourceCoupleExtension χ ζ R L γ δ Q I f S τ t k =
      ∑' u : SourceCellIndex S, ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        P.maskedSourceSpectralAmplitude ζ f u.1 u.2.val k ξ *
          R.coupleExtension χ L γ δ (P.spectralLinks Q u.2.val ξ) I (t + τ) := by
  have hs := P.integrable_allCellMaskedCoupleSlice_of_uniformRootL1 hχ hc ζ R L γ δ Q I
    hI hbox f S hS hL hK hM hB h hN hb τ t k
  change Integrable (fun u => P.allCellMaskedSpectralAmplitude ζ f S k u *
    P.allCellCutoffCoupleKernel χ R L γ δ Q I S (t + τ) u) (Measure.count.prod volume) at hs
  change (∫ u, P.allCellMaskedSpectralAmplitude ζ f S k u *
    P.allCellCutoffCoupleKernel χ R L γ δ Q I S (t + τ) u ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hs, integral_countable hs.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

end WaveTurbulence.Incoh

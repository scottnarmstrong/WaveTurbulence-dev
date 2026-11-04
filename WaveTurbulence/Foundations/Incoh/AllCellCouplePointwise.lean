/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellCoupleDecay
public import WaveTurbulence.Foundations.Incoh.CouplePointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Pointwise recombination of the actual source couple extension

A finite physical root bound gives spectral integrability at every external
clock pair, including boundaries. Counting/Lebesgue Fubini is pointwise.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional pointwise Fubini typing for the actual all-cell couple family. -/
theorem MomentumTreeData.integrable_allCellCoupleSlice_of_uniformRootL1 {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
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
    (t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => P.allCellSpectralAmplitude ζ f S k u *
      P.allCellCoupleKernel R L γ δ Q I S t u) (sourceCellMeasure S) := by
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl contDiff_rootCutoff hasCompactSupport_rootCutoff
  have hKs : StronglyMeasurable (P.allCellCoupleKernel R L γ δ Q I S t) :=
    (P.stronglyMeasurable_allCellCoupleKernel R hL γ δ Q I hI S).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  apply integrable_mul_of_uniform_enorm_bound (sourceCellMeasure S)
    (P.allCellSpectralAmplitude ζ f S k) (P.allCellCoupleKernel R L γ δ Q I S t)
    (P.integrable_allCellSpectralAmplitude ζ f S hS hK hM hB h k) hKs.aestronglyMeasurable
    (N := ENNReal.ofReal hc.bound ^ 4 * N) (ENNReal.mul_lt_top (by finiteness) hN)
  intro u
  exact (R.enorm_coupleExtension_le contDiff_rootCutoff hc hL γ δ (P.spectralLinks Q u.1.2.val u.2)
    hI hbox t).trans (mul_le_mul' le_rfl (hb _ _))

/-- The recombined spectral extension is the sum of the actual one-cell extensions at every time. -/
theorem MomentumTreeData.allCellSourceCoupleExtension_eq_tsum {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
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
    (t : Fin 2 → ℝ) (k : Mom d) :
    P.allCellSourceCoupleExtension ζ R L γ δ Q I f S t k =
      ∑' u : SourceCellIndex S, P.sourceCoupleExtension ζ R L γ δ Q I f u.1 u.2.val t k := by
  have hs := P.integrable_allCellCoupleSlice_of_uniformRootL1 ζ R L γ δ Q I hI hbox f S hS
    hL hK hM hB h hN hb t k
  change Integrable (fun u => P.allCellSpectralAmplitude ζ f S k u *
    P.allCellCoupleKernel R L γ δ Q I S t u) (Measure.count.prod volume) at hs
  change (∫ u, P.allCellSpectralAmplitude ζ f S k u * P.allCellCoupleKernel R L γ δ Q I S t u
    ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hs, integral_countable hs.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

end WaveTurbulence.Incoh

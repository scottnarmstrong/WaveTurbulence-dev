/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SingleRootSpectralAmplitude
public import WaveTurbulence.Foundations.Incoh.TreeAugmentedInputBounds
public import WaveTurbulence.Foundations.Incoh.MaskedCellActualMomentMass

/-! # The actual root-partition spectral family for a tree with its lone leaf -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Actual tree source amplitudes after adding and localizing the temporary root input. -/
@[expose] def MomentumTreeData.treeRootSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) : ℂ :=
  P.withRootInput.rootCutoffSpectralAmplitude ζ (appendRootInput f (treeRootPartition q)) S q k u

/-- Actual single-root derivative envelope, retaining its exact root-input Fourier moments. -/
@[expose] def treeRootSpectralEnvelope {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) : ℝ :=
  treeRootAmplitudeDerivativeFactor d J * maskedCellEnvelope J 0 (appendRootInput f (treeRootPartition q)) S u

theorem treeRootSpectralEnvelope_nonneg {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
    0 ≤ treeRootSpectralEnvelope J f S q u :=
  mul_nonneg (treeRootAmplitudeDerivativeFactor_nonneg _ _) (maskedCellEnvelope_nonneg _ _ _ _ _)

theorem MomentumTreeData.contDiff_treeRootSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
    ContDiff ℝ ∞ (fun k => P.treeRootSpectralAmplitude ζ f S q k u) :=
  P.withRootInput.contDiff_rootCutoffSpectralAmplitude ζ _ S q u

/-- The actual root cutoff supplies the local-model support identity. -/
theorem MomentumTreeData.treeRootSpectralAmplitude_eq_zero {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) (hq : treeRootCutoff q k = 0) :
    P.treeRootSpectralAmplitude ζ f S q k u = 0 := by
  simp only [treeRootSpectralAmplitude, rootCutoffSpectralAmplitude, hq, zero_mul]

/-- The actual amplitude derivatives are bounded by the proved root spectral envelope. -/
theorem MomentumTreeData.norm_iteratedFDeriv_treeRootSpectralAmplitude_le {d n m w J j : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (hj : j ≤ J) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (fun k => P.treeRootSpectralAmplitude ζ f S q k u) k‖ ≤
      treeRootSpectralEnvelope J f S q u :=
  P.withRootInput.norm_iteratedFDeriv_rootCutoffSpectralAmplitude_le ζ _ S q hj k u

/-- Actual single-root derivative slices satisfy the full counted spectral measurability. -/
theorem MomentumTreeData.stronglyMeasurable_treeRootAmplitudeDerivative {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (q : Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ) =>
      iteratedFDeriv ℝ j (fun k => P.treeRootSpectralAmplitude ζ f S q k u) k) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  exact P.withRootInput.stronglyMeasurable_rootCutoffAmplitudeDerivative ζ _ S hK hBq.le hq q k j

/-- Actual single-root envelopes are measurable from the original finite source input bounds. -/
theorem measurable_treeRootSpectralEnvelope {d n m K M : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    Measurable (treeRootSpectralEnvelope J f S q) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  exact measurable_const.mul (measurable_maskedCellEnvelope J 0 _ S hK hBq.le hq)

/-- Actual single-root envelopes are integrable; the translated input's norm is used only
for typing and will not enter the uniform mass bound. -/
theorem integrable_treeRootSpectralEnvelope {d n m K M : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    Integrable (treeRootSpectralEnvelope J f S q) (sourceCellMeasure S) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  exact (integrable_maskedCellEnvelope J 0 _ S hS hK (by omega) hBq.le hq).const_mul _

end WaveTurbulence.Incoh

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SingleRootSpectralAmplitude
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeAugmentedInputBounds
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellActualMomentMass

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootSpectralFamily` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # The actual root-partition spectral family for a tree with its lone leaf -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual tree source amplitudes after adding and localizing the temporary root input. -/
@[expose] def MomentumTreeData.treeRootSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) : ℂ :=
  (MomentumTreeData.rootCutoffSpectralAmplitudeSpatial (P := P.withRootInput)) ζ (appendRootInputSpatial f (treeRootPartitionSpatial q)) S q k u

/-- Actual single-root derivative envelope, retaining its exact root-input Fourier moments. -/
@[expose] def treeRootSpectralEnvelopeSpatial {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) : ℝ :=
  treeRootAmplitudeDerivativeFactorSpatial d J * maskedCellEnvelopeSpatial J 0 (appendRootInputSpatial f (treeRootPartitionSpatial q)) S u

theorem treeRootSpectralEnvelope_nonnegSpatial {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
    0 ≤ treeRootSpectralEnvelopeSpatial J f S q u :=
  mul_nonneg (treeRootAmplitudeDerivativeFactor_nonnegSpatial _ _) (maskedCellEnvelope_nonnegSpatial _ _ _ _ _)

open WaveTurbulence.Incoh.MomentumTreeData in
theorem MomentumTreeData.contDiff_treeRootSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
    ContDiff ℝ ∞ (fun k => (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q k u) :=
  (MomentumTreeData.contDiff_rootCutoffSpectralAmplitudeSpatial (P := P.withRootInput)) ζ _ S q u

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual root cutoff supplies the local-model support identity. -/
theorem MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) (hq : treeRootCutoffSpatial q k = 0) :
    (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q k u = 0 := by
  simp only [treeRootSpectralAmplitudeSpatial, rootCutoffSpectralAmplitudeSpatial, hq, zero_mul]

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual amplitude derivatives are bounded by the proved root spectral envelope. -/
theorem MomentumTreeData.norm_iteratedFDeriv_treeRootSpectralAmplitude_leSpatial {d n m w J j : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (hj : j ≤ J) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q k u) k‖ ≤
      treeRootSpectralEnvelopeSpatial J f S q u :=
  (MomentumTreeData.norm_iteratedFDeriv_rootCutoffSpectralAmplitude_leSpatial (P := P.withRootInput)) ζ _ S q hj k u

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual single-root derivative slices satisfy the full counted spectral measurability. -/
theorem MomentumTreeData.stronglyMeasurable_treeRootAmplitudeDerivativeSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (q : Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ) =>
      iteratedFDeriv ℝ j (fun k => (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q k u) k) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
  exact (MomentumTreeData.stronglyMeasurable_rootCutoffAmplitudeDerivativeSpatial (P := P.withRootInput)) ζ _ S hK hBq.le hq q k j

/-- Actual single-root envelopes are measurable from the original finite source input bounds. -/
theorem measurable_treeRootSpectralEnvelopeSpatial {d n m K M : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    Measurable (treeRootSpectralEnvelopeSpatial J f S q) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
  exact measurable_const.mul (measurable_maskedCellEnvelopeSpatial J 0 _ S hK hBq.le hq)

/-- Actual single-root envelopes are integrable; the translated input's norm is used only
for typing and will not enter the uniform mass bound. -/
theorem integrable_treeRootSpectralEnvelopeSpatial {d n m K M : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    Integrable (treeRootSpectralEnvelopeSpatial J f S q) (sourceCellMeasure S) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
  exact (integrable_maskedCellEnvelopeSpatial J 0 _ S hS hK (by omega) hBq.le hq).const_mul _

end WaveTurbulence.Flower.IncTop
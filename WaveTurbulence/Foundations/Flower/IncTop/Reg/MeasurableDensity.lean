/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawMeasureInsertion

/-! Ported by source from C2-B-TOP `Cut2BReg.MeasurableDensity` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Measurable density representatives preserve the actual Fourier measure multiplier -/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

/-- Replace only an integrable density by its strongly measurable representative. -/
@[expose] def measurableDensity {V α : Type*} [MeasurableSpace V] [MeasurableSpace α]
    (F : SpatialMeasure V α) : SpatialMeasure V α where
  μ := F.μ
  sigmaFinite := inferInstance
  frequency := F.frequency
  frequency_measurable := F.frequency_measurable
  amplitude := F.amplitude_integrable.aestronglyMeasurable.mk F.amplitude
  amplitude_integrable := F.amplitude_integrable.congr F.amplitude_integrable.aestronglyMeasurable.ae_eq_mk

/-- The representative is an everywhere measurable function. -/
theorem measurable_measurableDensity {V α : Type*} [MeasurableSpace V] [MeasurableSpace α]
    (F : SpatialMeasure V α) : Measurable (measurableDensity F).amplitude :=
  F.amplitude_integrable.aestronglyMeasurable.measurable_mk

/-- The density replacement has precisely the same mass. -/
theorem mass_measurableDensity {V α : Type*} [MeasurableSpace V] [MeasurableSpace α]
    (F : SpatialMeasure V α) : (measurableDensity F).mass = F.mass := by
  apply integral_congr_ae
  exact (F.amplitude_integrable.aestronglyMeasurable.ae_eq_mk.fun_comp norm).symm

/-- The actual internal multiplier is unchanged at every momentum, not only almost everywhere. -/
theorem value_measurableDensity {d n : ℕ} {α : Type*} [MeasurableSpace α]
    (F : SpatialMeasure (PairedMomentum d n) α) (x : PairedMomentum d n) :
    (measurableDensity F).value x = F.value x := by
  apply integral_congr_ae
  filter_upwards [F.amplitude_integrable.aestronglyMeasurable.ae_eq_mk] with a ha
  exact congrArg (fun c : ℂ => c * (Real.fourierChar (inner ℝ (F.frequency a) x) : ℂ)) ha.symm

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Equality of all raw weighted operators, preserving the literal lattice/time expression. -/
theorem MomentumTreeData.weightedSourceIntegral_measurableDensity
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (F : SpatialMeasure (PairedMomentum d n) α) (ζ : Circle) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (k : Mom d) :
    (MomentumTreeData.weightedSourceIntegral (P := P)) (measurableDensity F) ζ L γ δ Q I f k =
      (MomentumTreeData.weightedSourceIntegral (P := P)) F ζ L γ δ Q I f k := by
  unfold weightedSourceIntegral weightedSourceTimeIntegrand
  simp_rw [value_measurableDensity]

end WaveTurbulence.Flower.IncTop
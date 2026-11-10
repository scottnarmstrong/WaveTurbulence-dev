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

end WaveTurbulence.Flower.IncTop
/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.CharacterMixture
/-! Convert every integrable C2-A density, without an extra measurability premise. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine
variable {V α : Type} [MeasurableSpace V] [MeasurableSpace α]

/-- The measurable representative changes neither the multiplier nor its mass. -/
def measurableDensity (F : SpatialMeasure V α) : SpatialMeasure V α where
  μ := F.μ
  sigmaFinite := inferInstance
  frequency := F.frequency
  frequency_measurable := F.frequency_measurable
  amplitude := F.amplitude_integrable.aestronglyMeasurable.mk F.amplitude
  amplitude_integrable := F.amplitude_integrable.congr
    F.amplitude_integrable.aestronglyMeasurable.ae_eq_mk

theorem measurable_measurableDensity (F : SpatialMeasure V α) :
    Measurable (measurableDensity F).amplitude :=
  F.amplitude_integrable.aestronglyMeasurable.measurable_mk

theorem mass_measurableDensity (F : SpatialMeasure V α) :
    (measurableDensity F).mass = F.mass := by
  apply integral_congr_ae
  exact (F.amplitude_integrable.aestronglyMeasurable.ae_eq_mk.fun_comp norm).symm

/-- Polar decomposition of an integrable complex density into a finite measure
and a bounded phase. Input frequencies are fixed before exterior momenta. -/
def spatialCharMix {d : ℕ} (S : SumintShape) (F : SpatialMeasure V α)
    (ν : V → S.VIdx → Mom d) (hν : Measurable ν)
    (phase : α → (Fin 4 → Mom d) → ℂ)
    (hphase : ∀ E, Measurable fun a => phase a E)
    (hphaseNorm : ∀ a E, ‖phase a E‖ ≤ 1) : CharMix S d :=
  toCharMix S (measurableDensity F) (measurable_measurableDensity F)
    ν hν phase hphase hphaseNorm

theorem spatialCharMix_mass {d : ℕ} (S : SumintShape) (F : SpatialMeasure V α)
    (ν : V → S.VIdx → Mom d) (hν : Measurable ν)
    (phase : α → (Fin 4 → Mom d) → ℂ)
    (hphase : ∀ E, Measurable fun a => phase a E)
    (hphaseNorm : ∀ a E, ‖phase a E‖ ≤ 1) :
    (spatialCharMix S F ν hν phase hphase hphaseNorm).mass = F.mass := by
  rw [spatialCharMix, toCharMix_mass, mass_measurableDensity]

theorem spatialCharMix_val {d : ℕ} (S : SumintShape) (F : SpatialMeasure V α)
    (ν : V → S.VIdx → Mom d) (hν : Measurable ν)
    (phase : α → (Fin 4 → Mom d) → ℂ)
    (hphase : ∀ E, Measurable fun a => phase a E)
    (hphaseNorm : ∀ a E, ‖phase a E‖ ≤ 1)
    (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (spatialCharMix S F ν hν phase hphase hphaseNorm).val L E x =
      ∫ a, F.amplitude a * phase a E * charOf S L (ν (F.frequency a)) x ∂F.μ := by
  rw [spatialCharMix, toCharMix_val]
  apply integral_congr_ae
  filter_upwards [F.amplitude_integrable.aestronglyMeasurable.ae_eq_mk] with a ha
  exact congrArg (fun c : ℂ => c * phase a E * charOf S L (ν (F.frequency a)) x) ha.symm
end WaveTurbulence.VineSpaceK

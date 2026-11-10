/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSpectralCoefficient

/-! # The common spatial sample measure for all localized couple cells

Leaf and link centers use counting measure, and the independent leaf
frequencies use ordinary product Lebesgue measure. Link centers are
restricted to the actual finite geometric cover.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp Links
open scoped ENNReal

/-- The sample contains both localization arrays and the independent leaf frequencies. -/
abbrev LeafSpatialSample (d n m : ℕ) :=
  ((Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ)) × (Fin m → Fin d → ℝ)

/-- The common measure is chosen before root momenta and temporal frequencies. -/
def leafSpatialMeasure (d n m : ℕ) : Measure (LeafSpatialSample d n m) :=
  (Measure.count : Measure ((Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ))).prod volume

end WaveTurbulence.RA1Leafwise

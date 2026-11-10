/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure

/-!
# A fixed measure for momentum-dependent source cell selections

All integer cell pairs are counted. A finite selection is retained as an
actual indicator in the amplitude, permitting its support to depend on
root momentum while the integration measure stays fixed.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- All actual integer leaf/link cell pairs, before selecting their finite active fibers. -/
abbrev UnrestrictedCellIndex (d n m : ℕ) :=
  (Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ)

/-- Fixed counting/Lebesgue measure, independent of every root momentum and selection. -/
@[expose] def unrestrictedCellMeasure (d n m : ℕ) :
    Measure (UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) :=
  Measure.count.prod volume

instance (d n m : ℕ) : SigmaFinite (unrestrictedCellMeasure d n m) := by
  unfold unrestrictedCellMeasure
  infer_instance

end WaveTurbulence.Incoh

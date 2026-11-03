/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.Measurability

/-!
# G1: Borel measurability of the smooth-data set

SEAL-PLAN §B.4 G1. The landed NLS proof already constructs this set by
countably many closed truncated-flow conditions on rapidly decreasing data.
Here its rescaled interval is chosen from the physical terminal time.
-/

public section

namespace WaveTurbulence.MainGlue
open MeasureTheory

/-- G1 in exactly the physical-time premises proposed by the seal plan. -/
theorem measurableSet_smoothDataSet {d : ℕ} {L α γ T : ℝ} (hL : 0 < L)
    (hT : 0 < T) (hα : α = L ^ (-γ)) :
    MeasurableSet (NLS.smoothDataSet (d := d) L α T) := by
  subst hα
  have hk := NLS.kineticTime_rpow_neg_pos hL γ
  exact NLS.measurableSet_smoothDataSet hL one_pos (div_pos hT hk) (by field_simp)

end WaveTurbulence.MainGlue

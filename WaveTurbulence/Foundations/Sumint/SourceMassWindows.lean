/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.EnlargedTimeBox

/-!
# Literal interval endpoints for the source factor masses

These abbreviate the exact enlarged input box. The source admissibility
premise places every time label strictly below Dsteps; no additional
interval-selection premise is introduced.
-/

public section

namespace WaveTurbulence.Sumint

/-- Lower endpoints of the source's fixed enlarged input intervals. -/
@[expose] def enlargedTimeLower {d : ℕ} (D : SumintDatum d) (c h : ℝ) : D.S.TVar → ℝ :=
  fun v => (D.q v:ℝ)-c-h

/-- Upper endpoints of the same intervals. -/
@[expose] def enlargedTimeUpper {d : ℕ} (D : SumintDatum d) (c h : ℝ) : D.S.TVar → ℝ :=
  fun v => (D.q v:ℝ)+1-c+h

/-- These named endpoints are exactly the box used in the explicit extension. -/
theorem enlargedInputTimeBox_eq_Icc {d : ℕ} (D : SumintDatum d) (c h : ℝ) :
    enlargedInputTimeBox D c h = Set.Icc (enlargedTimeLower D c h) (enlargedTimeUpper D c h) := rfl

/-- Every admissible source input label lies in the required finite range. -/
theorem admissible_time_label_lt {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {N : ℕ}
    (hD : D.Admissible A L γ η N) (v : D.S.TVar) : D.q v < N :=
  Nat.lt_of_succ_le (hD.2.2.2.2.2.2.2.1 v)

/-- The enlarged intervals are ordered whenever their enlargement is nonnegative. -/
theorem enlargedTimeLower_le_upper {d : ℕ} (D : SumintDatum d) (c : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (v : D.S.TVar) : enlargedTimeLower D c h v ≤ enlargedTimeUpper D c h v := by
  dsimp [enlargedTimeLower,enlargedTimeUpper]
  linarith only [hh]

end WaveTurbulence.Sumint

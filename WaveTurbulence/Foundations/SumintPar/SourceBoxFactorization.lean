/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorRegularity

/-!
# Exact integration of the source factor norms over an input box

Coordinatewise interval restrictions regroup with the same measure as
the source time variables. This yields an equality of nonnegative masses
before the additional static order constraints are used for bad gains.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- General coordinate evaluation of the source grouping. -/
theorem timeCoordinateGrouping_apply (S : SumintShape) (τ : S.TVar → ℝ)
    (a : FactorIdx S) (j : FactorCoordinate S a) :
    timeCoordinateGrouping S τ a j = τ (factorCoordinateTimeEquiv S ⟨a,j⟩) := by
  rcases a with i | (p | i)
  · fin_cases j
    rfl
  · fin_cases j <;> rfl
  · rfl

/-- Every source norm factor is nonnegative, including its gap multiplier. -/
theorem sourceTimeNormFactor_nonneg {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : FactorIdx D.S) (z : FactorCoordinate D.S a → ℝ) :
    0 ≤ sourceTimeNormFactor D L γ δ η p ν r t a z := by
  apply mul_nonneg _ _
  · rcases a with i | (a | i)
    · exact zero_le_one
    · change 0 ≤ pairGapAmplitude D η a (z 0,z 1)
      unfold pairGapAmplitude
      split_ifs
      · exact Real.rpow_nonneg (abs_nonneg _) _
      · exact zero_le_one
    · exact zero_le_one
  · rcases a with i | (a | i) <;> exact norm_nonneg _

end WaveTurbulence.SumintPar

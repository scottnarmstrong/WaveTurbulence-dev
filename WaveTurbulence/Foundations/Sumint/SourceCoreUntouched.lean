/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreCrude
public import WaveTurbulence.Foundations.Sumint.SourceCoreMeasure

/-!
# Untouched cores retain their full Lebesgue masses

No time-volume or counting estimate is applied to a core disjoint from
the fixed source times. Its mixed coordinate measure is exactly the
original product Lebesgue measure.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- An untouched core's entire fixed/free product measure is exactly volume. -/
theorem fixedCoordinateMeasure_core_pi_eq_volume {d : ℕ} (D : SumintDatum d)
    (s : Finset D.S.TVar) (x : D.S.TVar → ℝ) (b : FactorIdx D.S)
    (hb : b ∉ sourceExitCores D s) :
    (Measure.pi fun j => fixedCoordinateMeasure (s:Set D.S.TVar) x
      (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩)) = volume := by
  simp_rw [fixedCoordinateMeasure_core_eq_volume D s x b hb]
  rfl

/-- Untouched actual core integrals retain exactly their full native Lebesgue mass. -/
theorem lintegral_sourceCore_untouched_eq {d : ℕ} (D : SumintDatum d)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (s : Finset D.S.TVar) (x : D.S.TVar → ℝ) (b : FactorIdx D.S)
    (hb : b ∉ sourceExitCores D s) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z
      ∂Measure.pi (fun j => fixedCoordinateMeasure (s:Set D.S.TVar) x
        (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) =
      ∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z := by
  rw [fixedCoordinateMeasure_core_pi_eq_volume D s x b hb]

end WaveTurbulence.Sumint

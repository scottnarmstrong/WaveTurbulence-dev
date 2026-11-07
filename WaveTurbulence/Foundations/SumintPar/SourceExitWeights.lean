/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.EndpointAveraging
public import WaveTurbulence.Foundations.SumintPar.TimeExitMeasurability

/-!
# Measurable weights for the actual source lower and upper exits

The boolean flag selects the upper endpoint when true and the lower
endpoint otherwise. Every tie is averaged equally. Both endpoint
partitions are exact for every input-time vector and all weights are
measurable and bounded by one.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- A literal coordinate endpoint of one translated source input interval. -/
@[expose] def timeExitCoordinate {d : ℕ} (D : SumintDatum d) (upper : Bool)
    (v : D.S.TVar) (u : D.S.TVar → ℝ) : ℝ :=
  (D.q v:ℝ)+(if upper then 1 else 0)-u v

/-- The actual lower or upper intersection endpoint selected by the boolean flag. -/
@[expose] noncomputable def timeExitEndpoint {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (u : D.S.TVar → ℝ) : ℝ :=
  if upper then upperTimeExit D hI u else lowerTimeExit D hI u

/-- Averaging weight on a coordinate attaining the actual chosen source exit. -/
@[expose] noncomputable def timeExitWeight {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) : ℝ :=
  endpointMatchWeight (timeExitCoordinate D upper) (timeExitEndpoint D hI upper) v u

/-- Every literal source coordinate endpoint is continuous in the full input-time vector. -/
theorem continuous_timeExitCoordinate {d : ℕ} (D : SumintDatum d) (upper : Bool) (v : D.S.TVar) :
    Continuous (timeExitCoordinate D upper v) := by
  unfold timeExitCoordinate
  fun_prop

/-- Both actual intersection endpoints are continuous. -/
theorem continuous_timeExitEndpoint {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) (upper : Bool) :
    Continuous (timeExitEndpoint D hI upper) := by
  cases upper
  · exact continuous_lowerTimeExit D hI
  · exact continuous_upperTimeExit D hI

/-- Every actual source exit is attained at a literal input coordinate endpoint. -/
theorem timeExitEndpoint_attained {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) (upper : Bool)
    (u : D.S.TVar → ℝ) : ∃ v, timeExitEndpoint D hI upper u = timeExitCoordinate D upper v u := by
  cases upper
  · simpa [timeExitEndpoint,timeExitCoordinate] using lowerTimeExit_attained D hI u
  · simpa [timeExitEndpoint,timeExitCoordinate] using upperTimeExit_attained D hI u

/-- Actual source exit weights are measurable on the full input-time space. -/
theorem measurable_timeExitWeight {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) : Measurable (timeExitWeight D hI upper v) :=
  measurable_endpointMatchWeight _ _ (fun w => (continuous_timeExitCoordinate D upper w).measurable)
    (continuous_timeExitEndpoint D hI upper).measurable v

/-- Each actual source exit weight lies in the closed unit interval. -/
theorem timeExitWeight_mem_Icc {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) :
    timeExitWeight D hI upper v u ∈ Set.Icc (0:ℝ) 1 :=
  endpointMatchWeight_mem_Icc _ _ u (timeExitEndpoint_attained D hI upper u) v

/-- Both source endpoint weights form exact finite partitions of one. -/
theorem sum_timeExitWeight {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (u : D.S.TVar → ℝ) : ∑ v, timeExitWeight D hI upper v u = 1 :=
  sum_endpointMatchWeight _ _ u (timeExitEndpoint_attained D hI upper u)

/-- Any actual source endpoint formula splits exactly into the weighted coordinate formulas. -/
theorem timeExit_formula_eq_weighted_sum {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (u : D.S.TVar → ℝ) (H : ℝ → ℂ) :
    H (timeExitEndpoint D hI upper u) =
      ∑ v, (timeExitWeight D hI upper v u:ℂ)*H (timeExitCoordinate D upper v u) :=
  endpoint_formula_eq_weighted_sum _ _ u (timeExitEndpoint_attained D hI upper u) H

end WaveTurbulence.SumintPar

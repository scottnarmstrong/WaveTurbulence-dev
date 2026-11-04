/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedClockDomain

/-!
# Integrating a literal tree time-domain fiber

The selected unit box is redundant on the actual source fiber. This
identity retains all external and internal causal constraints exactly.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Selected source integration is exactly the ordered fiber integral. -/
theorem TreeClockFibers.integral_selectedSourcePhase {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    (phase : Fin (m + 2) → ℝ) (u : Fin T.selection.coordinates.restCount → ℝ) (t : Fin 2 → ℝ) :
    (∫ v in T.selection.coordinates.rootBox Q,
      (T.timeDomain ∩ R.causalRootCut t).indicator
        (fun w => Fourier.linearTimePhase phase (T.selection.coordinates.equiv w).1)
        (T.selection.coordinates.equiv.symm (v, u))) =
      T.remainingDomain.indicator (fun u =>
        ∫ v in orderedClockDomain (m + 2) (t 0) (t 1) ∩ causalIntervalFiber m (T.lower u) (T.upper u),
          Fourier.linearTimePhase phase v) u := by
  have hb : MeasurableSet (T.selection.coordinates.rootBox Q) := measurableSet_Icc
  by_cases hu : u ∈ T.remainingDomain
  · rw [indicator_of_mem hu, ← integral_indicator hb,
      ← integral_indicator ((measurableSet_orderedClockDomain _ _ _).inter
        (measurableSet_causalIntervalFiber _ _ _))]
    apply integral_congr_ae
    filter_upwards [] with v
    have he := T.mem_causalDomain_equiv_symm R hfirst hlast v u t
    by_cases hv : v ∈ orderedClockDomain (m + 2) (t 0) (t 1) ∩
        causalIntervalFiber m (T.lower u) (T.upper u)
    · have hi := he.mpr ⟨hu, hv⟩
      have hvbox := T.interval_mem_box u hu v hv.2.1
      rw [indicator_of_mem hvbox, indicator_of_mem hi, indicator_of_mem hv,
        MeasurableEquiv.apply_symm_apply]
    · have hi : T.selection.coordinates.equiv.symm (v, u) ∉ T.timeDomain ∩ R.causalRootCut t :=
        fun h => hv (he.mp h).2
      rw [indicator_of_notMem hv]
      by_cases hvbox : v ∈ T.selection.coordinates.rootBox Q
      · rw [indicator_of_mem hvbox, indicator_of_notMem hi]
      · rw [indicator_of_notMem hvbox]
  · rw [indicator_of_notMem hu]
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    have hi : T.selection.coordinates.equiv.symm (v, u) ∉ T.timeDomain ∩ R.causalRootCut t :=
      fun h => hu ((T.mem_causalDomain_equiv_symm R hfirst hlast v u t).mp h).1
    rw [indicator_of_notMem hi]
    rfl

end WaveTurbulence.Incoh

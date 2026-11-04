/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ShapeFacts
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic

/-!
# Measurability and volume of the literal sumint time polytope

Every integration variable belongs to a unit interval. The additional
strict ordering conditions are open half-spaces and do not enlarge its
volume. All claims concern the exact snapshot-5 domain.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The closed unit box of input times in the exact datum. -/
@[expose] def inputTimeBox {d : ℕ} (D : SumintDatum d) : Set (D.S.TVar → ℝ) :=
  Icc (fun v => (D.q v : ℝ)) (fun v => (D.q v : ℝ) + 1)

/-- The source polytope is measurable for every output triple. -/
theorem measurableSet_timeDom {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (t t' t'' : ℝ) : MeasurableSet (D.timeDom hI t t' t'') := by
  classical
  unfold SumintDatum.timeDom
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro v
    have hv : Measurable (fun τ : D.S.TVar → ℝ => τ v) := measurable_pi_apply v
    exact (measurableSet_le measurable_const hv).inter
      ((measurableSet_le hv measurable_const).inter (measurableSet_lt hv measurable_const))
  · apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const (measurable_pi_apply _)
    · apply MeasurableSet.iInter
      intro c
      apply MeasurableSet.iInter
      intro _
      exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

/-- The order restrictions only remove points from the input unit box. -/
theorem timeDom_subset_inputTimeBox {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (t t' t'' : ℝ) : D.timeDom hI t t' t'' ⊆ inputTimeBox D := by
  intro τ hτ
  exact ⟨fun v => (hτ.1 v).1, fun v => (hτ.1 v).2.1⟩

/-- The full input unit box has volume one, including all normal-block times. -/
theorem volume_inputTimeBox {d : ℕ} (D : SumintDatum d) : volume (inputTimeBox D) = 1 := by
  classical
  rw [inputTimeBox, Real.volume_Icc_pi]
  simp

/-- The actual time integration domain has volume at most one. -/
theorem volume_timeDom_le_one {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (t t' t'' : ℝ) : volume (D.timeDom hI t t' t'') ≤ 1 := by
  exact (measure_mono (timeDom_subset_inputTimeBox D hI t t' t'')).trans_eq
    (volume_inputTimeBox D)

end WaveTurbulence.Sumint

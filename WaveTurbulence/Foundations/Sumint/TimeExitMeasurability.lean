/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TimeExits
public import WaveTurbulence.Foundations.Sumint.ExponentialBoxPointwise
import Mathlib.Tactic

/-!
# Joint measurability of the explicit extension kernel

The finite exit extrema are continuous, even at changes of the attaining
index. Thus the literal closed and strict output inequalities define
measurable subsets of the joint input/output space.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The lower exit is a continuous finite maximum. -/
theorem continuous_lowerTimeExit {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) :
    Continuous (lowerTimeExit D hI) := by
  unfold lowerTimeExit
  exact Continuous.finset_sup'_apply _ (fun _ _ => continuous_const.sub (continuous_apply _))

/-- The upper exit is a continuous finite minimum. -/
theorem continuous_upperTimeExit {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) :
    Continuous (upperTimeExit D hI) := by
  unfold upperTimeExit
  exact Continuous.finset_inf'_apply _ (fun _ _ => continuous_const.sub (continuous_apply _))

/-- The rectangular kernel is jointly measurable in its input and output times. -/
theorem measurable_exit_exponentialBox {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) :
    Measurable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) =>
      exponentialBox (lowerTimeExit D hI p.1) (upperTimeExit D hI p.1)
        (p.1 (firstTime D hI)) p.2) := by
  simp_rw [exponentialBox_eq_ite]
  have ha : Measurable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) => lowerTimeExit D hI p.1) := (continuous_lowerTimeExit D hI).measurable.comp measurable_fst
  have hb : Measurable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) => upperTimeExit D hI p.1) := (continuous_upperTimeExit D hI).measurable.comp measurable_fst
  have hu : Measurable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) => p.1 (firstTime D hI)) :=
    (measurable_pi_apply _).comp measurable_fst
  have hz (j : Fin 3) : Measurable (fun p : (D.S.TVar → ℝ) × (Fin 3 → ℝ) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  apply Measurable.ite
  · exact (((measurableSet_le ha (hz 0)).inter (measurableSet_le (hz 0) hb)).inter
      ((measurableSet_lt (hz 1) hu).inter (measurableSet_lt (hz 2) hu)))
  · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp (((hz 0).neg.add (hz 1)).add (hz 2)))
  · exact measurable_const

end WaveTurbulence.Sumint

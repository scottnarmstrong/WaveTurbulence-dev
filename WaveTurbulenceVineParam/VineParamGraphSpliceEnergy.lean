/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSplice
public import WaveTurbulenceVineParam.VineParamRungFiberPhases
import Mathlib.Tactic

/-! # Exact fresh-atom negative Gamma rows under one source rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable {d : ℕ}

/-- The fresh upper row uses the four actual upper incidences. -/
theorem rungSpliceEnergy_upper (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d' : V) (P : RungPattern)
    (old : {e : β // e ≠ i ∧ e ≠ j} → Mom d) (z : Fin 6 → Mom d) :
    directedEnergy (rungSpliceEnds ends i j σ p q c d' P) (.inr 0) (rungSpliceLabels i j old z)=
      -(P.signs 0 : ℝ)*‖z 2‖^2-(P.signs 1 : ℝ)*‖z 3‖^2-
        (P.signs 3 : ℝ)*‖z 4‖^2+(P.signs 2 : ℝ)*‖z 0‖^2 := by
  unfold directedEnergy
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6,
    (energySign (rungSpliceEnds ends i j σ p q c d' P) _ e : ℝ)*‖rungSpliceLabels i j old z e‖^2)=_
  rw [Fintype.sum_sum_type]
  cases P
  all_goals simp [energySign,rungSpliceEnds,rungSpliceLabels,orientPair,
    RungPattern.signs,Fin.sum_univ_succ]
  all_goals ring

/-- The fresh lower row uses the actual mates of the two rung incidences. -/
theorem rungSpliceEnergy_lower (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d' : V) (P : RungPattern)
    (old : {e : β // e ≠ i ∧ e ≠ j} → Mom d) (z : Fin 6 → Mom d) :
    directedEnergy (rungSpliceEnds ends i j σ p q c d' P) (.inr 1) (rungSpliceLabels i j old z)=
      (P.signs 0 : ℝ)*‖z 2‖^2+(P.signs 1 : ℝ)*‖z 3‖^2+
        (P.signs 3 : ℝ)*‖z 5‖^2-(P.signs 2 : ℝ)*‖z 1‖^2 := by
  unfold directedEnergy
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6,
    (energySign (rungSpliceEnds ends i j σ p q c d' P) _ e : ℝ)*‖rungSpliceLabels i j old z e‖^2)=_
  rw [Fintype.sum_sum_type]
  cases P
  all_goals simp [energySign,rungSpliceEnds,rungSpliceLabels,orientPair,
    RungPattern.signs,Fin.sum_univ_succ]
  all_goals ring

end WaveTurbulence.Vine.Param

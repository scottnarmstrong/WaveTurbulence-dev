/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractRungSigns
import Mathlib.Tactic

/-! # Exact t/s contract phases at the two actual inserted atoms -/

public section
namespace WaveTurbulence.Vine.Param
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]

/-- The fresh lower atom is the exact contract s slot after the coordinate
sign normalization. No norm approximation or dimension restriction is used. -/
theorem normalizedSplice_s_phase {d : ℕ} (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d' : V) (P : RungPattern) (old : {e : β // e ≠ i ∧ e ≠ j} → Mom d)
    (ε : ℤ) (r before x y : Mom d) :
    directedEnergy (rungSpliceEnds ends i j σ p q c d' P) (.inr 1)
      (rungSpliceLabels i j old (spliceChartLabels P (ε • r) before (-x,y)))=
        -2*inner ℝ x y := by
  rw [rungSpliceEnergy_lower]
  change P.lowerPhase before (-x,y)=_
  rw [P.lowerPhase_eq]
  simp only [inner_neg_left]
  ring

/-- The fresh upper atom is the exact contract t slot, with the gap
correction expressed in the fixed normalized coordinates. -/
theorem normalizedSplice_t_phase {d : ℕ} (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d' : V) (P : RungPattern) (old : {e : β // e ≠ i ∧ e ≠ j} → Mom d)
    (ε : ℤ) (r before x y : Mom d) :
    directedEnergy (rungSpliceEnds ends i j σ p q c d' P) (.inr 0)
      (rungSpliceLabels i j old (spliceChartLabels P (ε • r) before (-x,y)))=
        2*inner ℝ x y+2*inner ℝ r
          ((P.contractCorrection ε 0 : ℝ) • x+(P.contractCorrection ε 1 : ℝ) • y+
            (P.contractCorrection ε 2 : ℝ) • r) := by
  rw [rungSpliceEnergy_upper]
  change P.upperPhase (ε • r) before (-x,y)=_
  rw [P.upperPhase_eq,P.contractCorrection_phase]
  simp only [inner_neg_left]
  ring

end WaveTurbulence.Vine.Param

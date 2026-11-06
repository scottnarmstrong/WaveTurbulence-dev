/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSpliceEnergy
import Mathlib.Tactic

/-! # Source flow in the inserted graph produces its full local rung fiber -/

public section
namespace WaveTurbulence.Vine.Param
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- The two actual new differences, selected independently of old graph labels. -/
@[expose] def spliceRungCoordinates (P : RungPattern) (z : Fin 6 → E) : E×E :=
  P.encode (z 1) (z 2,z 3)

/-- Conservation at both fresh atoms, with its actual preceding gap, gives
exactly the local source fiber. No decoder or phase identity is a premise. -/
@[expose] def spliceRungCell (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d : V) (P : RungPattern) (old : {e : β // e ≠ i ∧ e ≠ j} → E)
    (z : Fin 6 → E) (r : E) (hgap : z 0=P.upperBefore r (z 1))
    (hu : directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inr 0) (rungSpliceLabels i j old z)=0)
    (hl : directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inr 1) (rungSpliceLabels i j old z)=0) :
    RungFlowFiber P r (z 1) := by
  refine ⟨((z 2,z 3),(z 4,z 5)),?_,?_⟩
  · rw [rungSpliceFlow_upper,hgap] at hu
    exact hu
  · rw [rungSpliceFlow_lower] at hl
    exact neg_eq_zero.mp hl

/-- The inserted pair's exact lower resonance in the actual graph labels. -/
theorem spliceRungCell_lower_phase {d : ℕ} (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d' : V) (P : RungPattern) (old : {e : β // e ≠ i ∧ e ≠ j} → Mom d)
    (z : Fin 6 → Mom d) (r : Mom d) (hgap : z 0=P.upperBefore r (z 1))
    (hu : directedFlow (rungSpliceEnds ends i j σ p q c d' P) (.inr 0) (rungSpliceLabels i j old z)=0)
    (hl : directedFlow (rungSpliceEnds ends i j σ p q c d' P) (.inr 1) (rungSpliceLabels i j old z)=0) :
    directedEnergy (rungSpliceEnds ends i j σ p q c d' P) (.inr 1) (rungSpliceLabels i j old z)=
      2*inner ℝ (spliceRungCoordinates P z).1 (spliceRungCoordinates P z).2 := by
  let Q := spliceRungCell ends i j σ p q c d' P old z r hgap hu hl
  rw [rungSpliceEnergy_lower]
  exact rung_fiber_lower_phase P r (z 1) Q

/-- The inserted pair's exact upper resonance, including the physical gap. -/
theorem spliceRungCell_upper_phase {d : ℕ} (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d' : V) (P : RungPattern) (old : {e : β // e ≠ i ∧ e ≠ j} → Mom d)
    (z : Fin 6 → Mom d) (r : Mom d) (hgap : z 0=P.upperBefore r (z 1))
    (hu : directedFlow (rungSpliceEnds ends i j σ p q c d' P) (.inr 0) (rungSpliceLabels i j old z)=0)
    (hl : directedFlow (rungSpliceEnds ends i j σ p q c d' P) (.inr 1) (rungSpliceLabels i j old z)=0) :
    directedEnergy (rungSpliceEnds ends i j σ p q c d' P) (.inr 0) (rungSpliceLabels i j old z)=
      -2*inner ℝ (spliceRungCoordinates P z).1 (spliceRungCoordinates P z).2+
        2*inner ℝ r (P.correction r (spliceRungCoordinates P z)) := by
  let Q := spliceRungCell ends i j σ p q c d' P old z r hgap hu hl
  rw [rungSpliceEnergy_upper,hgap]
  exact rung_fiber_upper_phase P r (z 1) Q

end WaveTurbulence.Vine.Param

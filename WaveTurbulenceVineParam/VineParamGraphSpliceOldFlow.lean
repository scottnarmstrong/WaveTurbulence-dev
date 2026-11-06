/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamVertexWeights
import Mathlib.Tactic

/-! # Exact source momentum at every old atom after inserting a rung -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

omit [Fintype β] [DecidableEq β] in
/-- Remaining old incidences are simply transported by the cap permutation. -/
theorem rungSpliceFlow_rest (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d v : V) (P : RungPattern) (e : {e : β // e ≠ i ∧ e ≠ j}) (k : E) :
    (-energySign (rungSpliceEnds ends i j σ p q c d P) (.inl (σ v)) (.inl e)) • k=
      (-energySign ends v e.1) • k := by
  simp [energySign,rungSpliceEnds]

/-- The old-atom flow splits into transported old occurrences and four
endpoint-supported rail terms. Coincident ports need no distinctness assumption. -/
theorem rungSpliceFlow_old (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d v : V) (P : RungPattern)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) :
    directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl (σ v)) (rungSpliceLabels i j old z)=
      (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) • old e)+
      P.signs 2 • (vertexWeight (σ v) p (z 0)-vertexWeight (σ v) q (z 1))-
      P.signs 3 • (vertexWeight (σ v) c (z 4)-vertexWeight (σ v) d (z 5)) := by
  unfold directedFlow
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6,
    (-energySign (rungSpliceEnds ends i j σ p q c d P) _ e) • rungSpliceLabels i j old z e)=_
  rw [Fintype.sum_sum_type]
  simp only [rungSpliceLabels,Sum.elim_inl,rungSpliceFlow_rest]
  cases P
  all_goals simp [energySign,rungSpliceEnds,orientPair,
    RungPattern.signs,Fin.sum_univ_succ,vertexWeight,sub_smul,neg_smul]
  all_goals abel

end WaveTurbulence.Vine.Param

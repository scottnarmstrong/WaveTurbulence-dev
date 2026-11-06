/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphMolecule
public import WaveTurbulenceVineParam.VineParamRungSource
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-! # The exact directed graph obtained by inserting one rung at a two-edge cut

Two old crossing occurrences are replaced by four rail occurrences and two
rung occurrences. Cap reflection relabels the remaining old graph. The six
local directions are the actual balanced rung pattern, not decoration data.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]

/-- Remaining old bond occurrences after deleting the two selected cut edges. -/
@[expose] def SpliceEdge (i j : β) := {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6

instance (i j : β) : Fintype (SpliceEdge i j) :=
  inferInstanceAs (Fintype ({e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6))

instance (i j : β) : DecidableEq (SpliceEdge i j) :=
  inferInstanceAs (DecidableEq ({e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6))

/-- Forward orientation for sign +1 and reverse orientation for sign -1. -/
@[expose] def orientPair {A : Type*} (s : ℤ) (u v : A) : A×A :=
  if s=1 then (u,v) else (v,u)

/-- The exact one-rung replacement endpoints, with fresh upper/lower atoms.
Local edge order: preceding upper/lower rails, two rung bonds, following
upper/lower rails. Loops and parallel old occurrences remain distinct. -/
@[expose] def rungSpliceEnds (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d : V) (P : RungPattern) : SpliceEdge i j → (V ⊕ Fin 2)×(V ⊕ Fin 2)
  | .inl e => (.inl (σ (ends e.1).1),.inl (σ (ends e.1).2))
  | .inr a =>
      ![orientPair (P.signs 2) (.inl p) (.inr 0),
        orientPair (-P.signs 2) (.inl q) (.inr 1),
        orientPair (P.signs 0) (.inr 0) (.inr 1),
        orientPair (P.signs 1) (.inr 0) (.inr 1),
        orientPair (P.signs 3) (.inr 0) (.inl c),
        orientPair (-P.signs 3) (.inr 1) (.inl d)] a

/-- Old remaining labels together with the six actual inserted local labels. -/
@[expose] def rungSpliceLabels {E : Type*} (i j : β)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) : SpliceEdge i j → E :=
  Sum.elim old z

/-- Actual upper fresh-atom momentum is precisely the normalized source row. -/
theorem rungSpliceFlow_upper {E : Type*} [AddCommGroup E]
    (ends : β → V×V) (i j : β) (σ : V ≃ V) (p q c d : V) (P : RungPattern)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) :
    directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inr 0) (rungSpliceLabels i j old z)=
      P.signs 0 • z 2+P.signs 1 • z 3+P.signs 3 • z 4-P.signs 2 • z 0 := by
  unfold directedFlow
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6,
    (-energySign (rungSpliceEnds ends i j σ p q c d P) _ e) • rungSpliceLabels i j old z e)=_
  rw [Fintype.sum_sum_type]
  cases P
  all_goals simp [energySign,rungSpliceEnds,rungSpliceLabels,orientPair,
    RungPattern.signs,Fin.sum_univ_succ]
  all_goals abel

/-- Actual lower fresh-atom momentum is the opposite of the second source row. -/
theorem rungSpliceFlow_lower {E : Type*} [AddCommGroup E]
    (ends : β → V×V) (i j : β) (σ : V ≃ V) (p q c d : V) (P : RungPattern)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) :
    directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inr 1) (rungSpliceLabels i j old z)=
      -(P.signs 0 • z 2+P.signs 1 • z 3+P.signs 3 • z 5-P.signs 2 • z 1) := by
  unfold directedFlow
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6,
    (-energySign (rungSpliceEnds ends i j σ p q c d P) _ e) • rungSpliceLabels i j old z e)=_
  rw [Fintype.sum_sum_type]
  cases P
  all_goals simp [energySign,rungSpliceEnds,rungSpliceLabels,orientPair,
    RungPattern.signs,Fin.sum_univ_succ]
  all_goals abel

end WaveTurbulence.Vine.Param

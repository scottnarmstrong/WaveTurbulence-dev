/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRawSourceCell
import Mathlib.Tactic

/-! # The two actual degree-four source rows of an unnormalized rung cell -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β]

/-- Each source local occurrence has its signed endpoint degree contribution. -/
theorem rawCell_local_degree (rest : β → V×V) (p q c d : V) (s : Fin 6 → ℤ)
    (hs : ∀ i,s i=1 ∨ s i= -1) (v : V ⊕ Fin 2) (j : Fin 6) :
    -energySign (rawSourceCellEnds rest p q c d s) v (.inr j)=
      s j*((if (sourceCellPorts p q c d j).1=v then 1 else 0)-
        (if (sourceCellPorts p q c d j).2=v then 1 else 0)) :=
  degree_orientPair (s j) (hs j) _ _ v

/-- The upper fresh atom's actual outgoing-minus-incoming degree. -/
theorem rawCell_upper_degree (rest : β → V×V) (p q c d : V) (s : Fin 6 → ℤ)
    (hs : ∀ i,s i=1 ∨ s i= -1) :
    (∑ e,-energySign (rawSourceCellEnds rest p q c d s) (.inr 0) e)=s 2+s 3+s 4-s 0 := by
  rw [Fintype.sum_sum_type]
  have hr : ∀ e : β,-energySign (rawSourceCellEnds rest p q c d s) (.inr 0) (.inl e)=0 := by
    intro e
    simp [energySign,rawSourceCellEnds]
  simp only [hr,sum_const_zero,zero_add,rawCell_local_degree rest p q c d s hs]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [sourceCellPorts]
  ring

/-- The lower fresh atom's actual outgoing-minus-incoming degree. -/
theorem rawCell_lower_degree (rest : β → V×V) (p q c d : V) (s : Fin 6 → ℤ)
    (hs : ∀ i,s i=1 ∨ s i= -1) :
    (∑ e,-energySign (rawSourceCellEnds rest p q c d s) (.inr 1) e)=s 5-s 1-s 2-s 3 := by
  rw [Fintype.sum_sum_type]
  have hr : ∀ e : β,-energySign (rawSourceCellEnds rest p q c d s) (.inr 1) (.inl e)=0 := by
    intro e
    simp [energySign,rawSourceCellEnds]
  simp only [hr,sum_const_zero,zero_add,rawCell_local_degree rest p q c d s hs]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp [sourceCellPorts]
  ring

end WaveTurbulence.Vine.Param

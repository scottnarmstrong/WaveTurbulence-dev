/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphCutFlow
public import WaveTurbulenceVineParam.VineParamTwoEdgeDecomposition
import Mathlib.Tactic

/-! # The two directions across a balanced source cap are opposite -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]

/-- Summing the actual balanced degree rows over a cap forces its only two
crossing occurrences to have opposite directions. -/
theorem balanced_two_edge_directions (ends : β → V×V) (C : Finset V)
    (i j : β) (hij : i ≠ j) (p q c d : V)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (si sj : ℤ) (hsi : si=1 ∨ si= -1) (hsj : sj=1 ∨ sj= -1)
    (hi : ends i=orientPair si p c) (hj : ends j=orientPair sj q d)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (hbal : ∀ v,(∑ e,-energySign ends v e)=0) : si+sj=0 := by
  have hz : (∑ e,cutSign ends C e)=0 := by
    calc
      _=(∑ e,∑ v ∈ C,-energySign ends v e) := by simp only [sum_vertex_incidence]
      _=(∑ v ∈ C,∑ e,-energySign ends v e) := sum_comm
      _=0 := by simp only [hbal,sum_const_zero]
  rw [sum_two_edge_rest i j hij] at hz
  have hr : ∀ e : {e : β // e ≠ i ∧ e ≠ j},cutSign ends C e.1=0 := by
    intro e
    simp only [cutSign,hrest e.1 e.2.1 e.2.2,sub_self]
  simp only [hr,sum_const_zero,zero_add] at hz
  rcases hsi with rfl | rfl <;> rcases hsj with rfl | rfl
  all_goals simp [cutSign,hi,hj,orientPair,hp,hq,hc,hd] at hz ⊢

end WaveTurbulence.Vine.Param

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceLabelEquiv
import Mathlib.Tactic

/-! # The old cut's physical gap follows from source conservation -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- The two individually marked cut occurrences exhaust the cap flux. -/
theorem old_cut_flux (ends : β → V×V) (i j : β) (hij : i ≠ j)
    (s : ℤ) (hs : s=1 ∨ s= -1) (C : Finset V) (p q c d : V)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (hi : ends i=orientPair s p c) (hj : ends j=orientPair (-s) q d)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C)) (k : β → E) :
    (∑ e,cutSign ends C e • k e)= -s • k i+s • k j := by
  rw [sum_two_edge_rest i j hij]
  have hr : ∀ e : {e : β // e ≠ i ∧ e ≠ j},cutSign ends C e.1=0 := by
    intro e
    simp only [cutSign,hrest e.1 e.2.1 e.2.2,sub_self]
  simp only [hr,zero_zsmul,sum_const_zero,zero_add]
  rcases hs with rfl | rfl <;> simp [cutSign,hi,hj,orientPair,hp,hq,hc,hd]

/-- Every old source label fiber already satisfies the precise preceding
rail gap required by insertion; no additional decoration premise is needed. -/
theorem old_cut_preceding_gap (ends : β → V×V) (i j : β) (hij : i ≠ j)
    (P : RungPattern) (C : Finset V) (p q c d a b : V) (hab : a ≠ b)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (hi : ends i=orientPair (P.signs 2) p c) (hj : ends j=orientPair (-P.signs 2) q d)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (k : β → E) (r : E) (ha : directedFlow ends a k= -r) (hb : directedFlow ends b k=r)
    (hz : ∀ v ∈ C,v ≠ a → v ≠ b → directedFlow ends v k=0) :
    k i=P.upperBefore (spliceGap C a b r) (k j) := by
  have hs : P.signs 2=1 ∨ P.signs 2= -1 := by cases P <;> decide
  have hf := cap_flow_from_joints ends C k a b hab hz
  rw [old_cut_flux ends i j hij _ hs C p q c d hp hq hc hd hi hj hrest k,ha,hb] at hf
  have hh : -(P.signs 2) • k i+P.signs 2 • k j= -spliceGap C a b r := by
    rw [hf]
    by_cases hca : a ∈ C <;> by_cases hcb : b ∈ C <;> simp [spliceGap,hca,hcb]
  apply P.upperBefore_of_gap
  simpa only [neg_add,neg_smul,neg_neg,smul_sub,sub_eq_add_neg,smul_add,smul_neg] using congrArg Neg.neg hh

end WaveTurbulence.Vine.Param

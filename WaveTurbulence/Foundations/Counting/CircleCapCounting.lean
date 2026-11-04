/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleOctantGeometry
import Mathlib.Tactic

/-!
# Exact counts of outer circular caps

The vertical outer caps are counted by their actual closed integer slices.
The central square includes the artificial edges, so the cap column cut is
strict. These identities precede any exponential-sum estimate.
-/

public section

namespace WaveTurbulence.Counting

/-- Restricting a disc by a condition on its first coordinate restricts
precisely the integer column set in its vertical slicing formula. -/
theorem card_latticeDisc_filter_first (c : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    (p : ℤ → Prop) [DecidablePred p] :
    ((latticeDisc c R).filter (fun n => p (n 0))).card =
      ∑ x ∈ (integerInterval (c 0-R) (c 0+R)).filter p,
        (integerInterval (c 1-circleHeight R (c 0) x)
          (c 1+circleHeight R (c 0) x)).card := by
  classical
  have he : (latticeDisc c R).filter (fun n => p (n 0)) =
      ((integerInterval (c 0-R) (c 0+R)).filter p).biUnion (fun x =>
        (integerInterval (c 1-circleHeight R (c 0) x)
          (c 1+circleHeight R (c 0) x)).map (columnEmbedding x)) := by
    ext n
    simp only [Finset.mem_filter,mem_latticeDisc_iff_intervals,Finset.mem_biUnion,Finset.mem_map]
    constructor
    · rintro ⟨⟨hx,hy⟩,hp⟩
      refine ⟨n 0,⟨hx,hp⟩,n 1,hy,?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨x,⟨hx,hp⟩,y,hy,hn⟩
      have hx0 : x = n 0 := congrFun hn 0
      have hy1 : y = n 1 := congrFun hn 1
      subst x
      subst y
      exact ⟨⟨hx,hy⟩,hp⟩
  rw [he,Finset.card_biUnion]
  · simp only [Finset.card_map]
  · intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hn
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hm
    exact hxy ((congrFun hi 0).trans (congrFun hj 0).symm)

/-- Exact height-minus-sawtooth formula for the two vertical outer caps. -/
theorem card_latticeDisc_vertical_caps_eq (c : EuclideanSpace ℝ (Fin 2)) (R T : ℝ) :
    (((latticeDisc c R).filter (fun n => T < |(n 0:ℝ)-c 0|)).card:ℝ) =
      ∑ x ∈ (integerInterval (c 0-R) (c 0+R)).filter (fun x : ℤ => T < |(x:ℝ)-c 0|),
        (2*circleHeight R (c 0) x-
          NumberTheory.sawtooth (circleHeight R (c 0) x+c 1)-
          NumberTheory.sawtooth (circleHeight R (c 0) x-c 1)) := by
  classical
  rw [card_latticeDisc_filter_first c R (fun x : ℤ => T < |(x:ℝ)-c 0|),Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hh : 0 ≤ circleHeight R (c 0) x := Real.sqrt_nonneg _
  rw [card_integerInterval_eq_sawtooth (by linarith only [hh]),neg_sub]
  rw [show c 1+circleHeight R (c 0) x = circleHeight R (c 0) x+c 1 by ring]
  ring

end WaveTurbulence.Counting

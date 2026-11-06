/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSplice
import Mathlib.Tactic

/-! # Recovering the complete six-edge pattern from source balanced degrees

The cap balance is the two-edge cut equation for the original old cap.
No decoration or already normalized orientation is assumed.
-/

public section
namespace WaveTurbulence.Vine.Param

/-- The complete local orientation is forced by both degree-four rows and
the two-edge cap cut. Order: before upper/lower, rung0/rung1, after upper/lower. -/
theorem exists_splice_orientation (s : Fin 6 → ℤ)
    (hs : ∀ i,s i=1 ∨ s i= -1)
    (hu : s 2+s 3+s 4-s 0=0)
    (hl : s 5-s 1-s 2-s 3=0)
    (hcap : s 4+s 5=0) :
    ∃ P : RungPattern,s=![P.signs 2,-P.signs 2,P.signs 0,P.signs 1,P.signs 3,-P.signs 3] := by
  obtain ⟨P,hP⟩ := RungPattern.signs_exhaustive ![s 2,s 3,s 0,s 4]
    (by intro i; fin_cases i <;> exact hs _)
    (by change s 2+s 3+s 4-s 0=0; exact hu)
  have h0 := congrFun hP 0
  have h1 := congrFun hP 1
  have h2 := congrFun hP 2
  have h3 := congrFun hP 3
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2 h3
  refine ⟨P,?_⟩
  funext i
  fin_cases i
  · exact h2.symm
  · change s 1= -P.signs 2
    omega
  · exact h0.symm
  · exact h1.symm
  · exact h3.symm
  · change s 5= -P.signs 3
    omega

end WaveTurbulence.Vine.Param

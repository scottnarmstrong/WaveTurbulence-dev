/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract

/-! # Actual chart slot coverage and distinctness for all vine types -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {X : VineType}

/-- Joint, x, y and normal core slots exhaust every chart, including the
minimal typeII and the empty typeI ladder. -/
theorem chart_shape_cover (A : Shape X) (i : Fin A.n) :
    i = A.x0 ∨ (∃ j, i = A.xSlot j) ∨ (∃ j, i = A.ySlot j) ∨
      ∃ (hn : X.IsBad = false) (c : Fin 3), i = A.uSlot hn c := by
  by_cases hz : i.val = 0
  · exact Or.inl (Fin.ext hz)
  · right
    by_cases hx : i.val < A.m+1
    · left
      refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩
      change i.val = i.val-1+1
      omega
    · right
      by_cases hy : i.val < 2*A.m+1
      · left
        refine ⟨⟨i.val-(A.m+1),by omega⟩,Fin.ext ?_⟩
        change i.val = A.m+1+(i.val-(A.m+1))
        omega
      · right
        have hn : X.IsBad = false := by
          cases h : X.IsBad
          · rfl
          · have hi := i.isLt
            simp only [Shape.n,h,ite_true] at hi
            omega
        refine ⟨hn,⟨i.val-(2*A.m+1),?_⟩,Fin.ext ?_⟩
        · have hi := i.isLt
          simp only [Shape.n,hn,Bool.false_eq_true,ite_false] at hi
          omega
        · change i.val = 2*A.m+1+(i.val-(2*A.m+1))
          omega

theorem chart_x_ne_y (A : Shape X) (j : Fin A.m) : A.xSlot j ≠ A.ySlot j := by
  intro h
  have he := congrArg Fin.val h
  change j.val+1 = A.m+1+j.val at he
  omega

theorem chart_u_ne (A : Shape X) (hn : X.IsBad = false) {i j : Fin 3} (h : i ≠ j) :
    A.uSlot hn i ≠ A.uSlot hn j := by
  intro he
  apply h
  apply Fin.ext
  have hh := congrArg Fin.val he
  change 2*A.m+1+i.val = 2*A.m+1+j.val at hh
  omega

end WaveTurbulence.VineEstS2

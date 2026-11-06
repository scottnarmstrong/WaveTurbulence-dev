/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamExpandSym
import Mathlib.Tactic

/-! # The order preserving atom relabeling that removes two atoms -/

public section
namespace WaveTurbulence.Vine.Param

/-- Inverse of `skip2`: re-insert the two removed positions. -/
@[expose] def unskip2 (f0 f1 u : ℕ) : ℕ :=
  if f1 ≤ (if f0 ≤ u then u+1 else u) then (if f0 ≤ u then u+1 else u)+1
  else (if f0 ≤ u then u+1 else u)

theorem skip2_unskip2 (f0 f1 u : ℕ) (h : f0 < f1) : skip2 f0 f1 (unskip2 f0 f1 u) = u := by
  simp only [skip2,unskip2]
  split_ifs <;> omega

theorem unskip2_skip2 (f0 f1 t : ℕ) (h : f0 < f1) (h0 : t ≠ f0) (h1 : t ≠ f1) :
    unskip2 f0 f1 (skip2 f0 f1 t) = t := by
  simp only [skip2,unskip2]
  split_ifs <;> omega

theorem skip2_lt_of_ne (n f0 f1 t : ℕ) (h : f0 < f1) (h1 : f1 < n+2) (ht : t < n+2)
    (h0' : t ≠ f0) (h1' : t ≠ f1) : skip2 f0 f1 t < n := by
  simp only [skip2]; split_ifs <;> omega

theorem unskip2_lt (n f0 f1 u : ℕ) (h : f0 < f1) (h1 : f1 < n+2) (hu : u < n) :
    unskip2 f0 f1 u < n+2 := by
  simp only [unskip2]; split_ifs <;> omega

/-- Removing two atoms from `Fin (n+2)`. -/
@[expose] def skipEquiv (n f0 f1 : ℕ) (h : f0 < f1) (h1 : f1 < n+2) : Fin (n+2) ≃ Fin n ⊕ Fin 2 where
  toFun t := if h0 : t.1 = f0 then Sum.inr 0 else if h1' : t.1 = f1 then Sum.inr 1
    else Sum.inl ⟨skip2 f0 f1 t.1,skip2_lt_of_ne n f0 f1 t.1 h h1 t.2 h0 h1'⟩
  invFun := Sum.elim (fun u => ⟨unskip2 f0 f1 u.1,unskip2_lt n f0 f1 u.1 h h1 u.2⟩)
    (fun i => if i = 0 then ⟨f0,by omega⟩ else ⟨f1,h1⟩)
  left_inv := by
    intro t
    by_cases h0 : t.1 = f0
    · simp only [h0,dite_true,Sum.elim_inr,if_true]
      exact Fin.ext h0.symm
    · by_cases h1' : t.1 = f1
      · dsimp only
        rw [dif_neg h0,dif_pos h1']
        have : (1 : Fin 2) ≠ 0 := by decide
        simp only [Sum.elim_inr,this,if_false]
        exact Fin.ext h1'.symm
      · simp only [h0,h1',dite_false,Sum.elim_inl]
        exact Fin.ext (unskip2_skip2 f0 f1 t.1 h h0 h1')
  right_inv := by
    intro w
    rcases w with u | i
    · have e1 := skip2_unskip2 f0 f1 u.1 h
      have e2 : unskip2 f0 f1 u.1 ≠ f0 ∧ unskip2 f0 f1 u.1 ≠ f1 := by
        simp only [unskip2]; split_ifs <;> omega
      simp only [Sum.elim_inl]
      simp [e2.1,e2.2]
      exact Fin.ext e1
    · fin_cases i
      · simp
      · simp; omega

end WaveTurbulence.Vine.Param

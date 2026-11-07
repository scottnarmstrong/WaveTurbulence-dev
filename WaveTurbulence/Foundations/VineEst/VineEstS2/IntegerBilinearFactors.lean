/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

/-! # Primitive integer factors of one independent bilinear coordinate pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- Comparing diagonal and polarized coefficients of L₁L₂=xᵢxⱼ forces
both integer linear factors to be coordinate forms, up to a common sign
and exchange. This will recover local witnesses from pure phase identities. -/
theorem integer_bilinear_factors {α : Type*} [DecidableEq α]
    (a b : α → ℤ) (i j : α)
    (hdiagI : a i*b i = 0) (hdiagJ : a j*b j = 0)
    (hc : a i*b j+a j*b i = 1)
    (hI : ∀ k, a i*b k+a k*b i = if k = j then 1 else 0)
    (hJ : ∀ k, a j*b k+a k*b j = if k = i then 1 else 0) :
    (∃ ε : ℤˣ, (∀ k, a k = (ε : ℤ)*(if k = i then 1 else 0)) ∧
      ∀ k, b k = (ε : ℤ)*(if k = j then 1 else 0)) ∨
    (∃ ε : ℤˣ, (∀ k, a k = (ε : ℤ)*(if k = j then 1 else 0)) ∧
      ∀ k, b k = (ε : ℤ)*(if k = i then 1 else 0)) := by
  rcases mul_eq_zero.mp hdiagI with hai | hbi
  · have hp : a j*b i = 1 := by simpa only [hai,zero_mul,zero_add] using hc
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hp with ⟨haj,hbi⟩ | ⟨haj,hbi⟩
    · have hbj : b j = 0 := by simpa only [haj,one_mul] using hdiagJ
      right
      refine ⟨1,?_,?_⟩ <;> intro k
      · have hk := hI k
        simp only [hai,hbi,zero_mul,mul_one,zero_add] at hk
        simpa only [Units.val_one,one_mul] using hk
      · have hk := hJ k
        simp only [haj,hbj,one_mul,mul_zero,add_zero] at hk
        simpa only [Units.val_one,one_mul] using hk
    · have hbj : b j = 0 := by rw [haj,neg_one_mul] at hdiagJ; omega
      right
      refine ⟨-1,?_,?_⟩ <;> intro k
      · have hk := hI k
        simp only [hai,hbi,zero_mul,mul_neg_one,zero_add] at hk
        simp only [Units.val_neg,Units.val_one,neg_one_mul]
        omega
      · have hk := hJ k
        simp only [haj,hbj,neg_one_mul,mul_zero,add_zero] at hk
        simp only [Units.val_neg,Units.val_one,neg_one_mul]
        omega
  · have hp : a i*b j = 1 := by simpa only [hbi,mul_zero,add_zero] using hc
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hp with ⟨hai,hbj⟩ | ⟨hai,hbj⟩
    · have haj : a j = 0 := by simpa only [hbj,mul_one] using hdiagJ
      left
      refine ⟨1,?_,?_⟩ <;> intro k
      · have hk := hJ k
        simp only [haj,hbj,zero_mul,mul_one,zero_add] at hk
        simpa only [Units.val_one,one_mul] using hk
      · have hk := hI k
        simp only [hai,hbi,one_mul,mul_zero,add_zero] at hk
        simpa only [Units.val_one,one_mul] using hk
    · have haj : a j = 0 := by rw [hbj,mul_neg_one] at hdiagJ; omega
      left
      refine ⟨-1,?_,?_⟩ <;> intro k
      · have hk := hJ k
        simp only [haj,hbj,zero_mul,mul_neg_one,zero_add] at hk
        simp only [Units.val_neg,Units.val_one,neg_one_mul]
        omega
      · have hk := hI k
        simp only [hai,hbi,neg_one_mul,mul_zero,add_zero] at hk
        simp only [Units.val_neg,Units.val_one,neg_one_mul]
        omega

end WaveTurbulence.VineEstS2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.IntegerBilinearFactors
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Recover primitive integer local factors from a pure phase identity -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
variable {α : Type*} [Fintype α] [DecidableEq α]

def integerLinearForm (a x : α → ℤ) : ℤ := ∑ k, a k*x k

theorem integerLinearForm_single (a : α → ℤ) (i : α) :
    integerLinearForm a (Pi.single i 1) = a i := by
  classical
  simp [integerLinearForm,Pi.single_apply]

omit [DecidableEq α] in
theorem integerLinearForm_add (a x y : α → ℤ) :
    integerLinearForm a (x+y) = integerLinearForm a x+integerLinearForm a y := by
  simp only [integerLinearForm,Pi.add_apply,mul_add,Finset.sum_add_distrib]

/-- No local-tag or inverse-coefficient assumption is made. The uniform
pure phase identity itself identifies the two integer factors. -/
theorem integer_linear_phase_factors (a b : α → ℤ) (i j : α) (hij : i ≠ j)
    (hprod : ∀ x : α → ℤ, integerLinearForm a x*integerLinearForm b x = x i*x j) :
    (∃ ε : ℤˣ, (∀ k, a k = (ε : ℤ)*(if k = i then 1 else 0)) ∧
      ∀ k, b k = (ε : ℤ)*(if k = j then 1 else 0)) ∨
    (∃ ε : ℤˣ, (∀ k, a k = (ε : ℤ)*(if k = j then 1 else 0)) ∧
      ∀ k, b k = (ε : ℤ)*(if k = i then 1 else 0)) := by
  have hdiag (k : α) : a k*b k = 0 := by
    have he := hprod (Pi.single k 1)
    rw [integerLinearForm_single,integerLinearForm_single] at he
    by_cases hki : k = i
    · subst k
      simpa [Pi.single_apply,hij,Ne.symm hij] using he
    · simpa [Pi.single_apply,hki,Ne.symm hki] using he
  have hcross (k l : α) : a k*b l+a l*b k =
      (if i = k then 1 else 0)*(if j = l then 1 else 0) +
      (if i = l then 1 else 0)*(if j = k then 1 else 0) := by
    have hkl := hprod (Pi.single k 1+Pi.single l 1)
    have hk := hprod (Pi.single k 1)
    have hl := hprod (Pi.single l 1)
    simp only [integerLinearForm_add,integerLinearForm_single,Pi.add_apply,Pi.single_apply] at hkl hk hl
    linear_combination hkl-hk-hl
  apply integer_bilinear_factors a b i j (hdiag i) (hdiag j)
  · simpa only [eq_comm,ite_true,ite_false,hij,Ne.symm hij,mul_one,mul_zero,zero_mul,add_zero] using hcross i j
  · intro k
    simpa only [eq_comm,ite_true,ite_false,hij,Ne.symm hij,mul_one,mul_zero,zero_mul,one_mul,add_zero] using hcross i k
  · intro k
    simpa only [eq_comm,ite_true,ite_false,hij,Ne.symm hij,mul_one,mul_zero,zero_mul,one_mul,zero_add] using hcross j k

end WaveTurbulence.VineEstS2

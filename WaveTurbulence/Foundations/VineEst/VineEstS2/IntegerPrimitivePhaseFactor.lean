/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.IntegerLinearPhaseFactors

/-! # One primitive phase factor recovers a literal free coordinate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem unit_of_product_sign (a b c : ℤ) (hp : a*b = c) (hc : c = 1 ∨ c = -1) :
    a = 1 ∨ a = -1 := by
  rcases hc with hc | hc
  · exact Int.eq_one_or_neg_one_of_mul_eq_one (hp.trans hc)
  · apply Int.eq_one_or_neg_one_of_mul_eq_one (v := -b)
    rw [mul_neg,hp,hc,neg_neg]

/-- This includes nonlinear core products xᵢ(xⱼ+xₖ-xᵢ): only one other
unit coefficient is needed. The second factor need not be a coordinate. -/
theorem integer_primitive_phase_factor (a b c : α → ℤ) (i j : α) (hji : j ≠ i)
    (hc : c j = 1 ∨ c j = -1)
    (hprod : ∀ x : α → ℤ, integerLinearForm a x*integerLinearForm b x = x i*integerLinearForm c x) :
    ((a i = 1 ∨ a i = -1) ∧ ∀ k, a k = a i*(if k = i then 1 else 0)) ∨
    ((b i = 1 ∨ b i = -1) ∧ ∀ k, b k = b i*(if k = i then 1 else 0)) := by
  have hj : a j*b j = 0 := by
    have he := hprod (Pi.single j 1)
    simpa [integerLinearForm_single,Pi.single_apply,hji,Ne.symm hji] using he
  have hcross (k : α) : a j*b k+a k*b j = (if i = k then 1 else 0)*c j := by
    have hsum := hprod (Pi.single j 1+Pi.single k 1)
    have hj' := hprod (Pi.single j 1)
    have hk := hprod (Pi.single k 1)
    simp only [integerLinearForm_add,integerLinearForm_single,Pi.add_apply,Pi.single_apply] at hsum hj' hk
    simp only [Ne.symm hji,ite_false,zero_add,zero_mul] at hsum hj'
    linear_combination hsum-hj'-hk
  rcases mul_eq_zero.mp hj with haj | hbj
  · have hp : a i*b j = c j := by simpa only [haj,zero_mul,zero_add,ite_true,one_mul] using hcross i
    have hai := unit_of_product_sign _ _ _ hp hc
    have hbj : b j ≠ 0 := by intro h; rw [h,mul_zero] at hp; rcases hc with hc | hc <;> omega
    left
    refine ⟨hai,?_⟩
    intro k
    by_cases hki : k = i
    · simp only [hki,ite_true,mul_one]
    · have hk : a k*b j = 0 := by simpa only [haj,zero_mul,zero_add,hki,Ne.symm hki,ite_false,zero_mul] using hcross k
      have ha := (mul_eq_zero.mp hk).resolve_right hbj
      simp only [ha,hki,Ne.symm hki,ite_false,mul_zero]
  · have hp : a j*b i = c j := by simpa only [hbj,mul_zero,add_zero,ite_true,one_mul] using hcross i
    have hbi := unit_of_product_sign _ _ _ ((mul_comm _ _).trans hp) hc
    have haj : a j ≠ 0 := by intro h; rw [h,zero_mul] at hp; rcases hc with hc | hc <;> omega
    right
    refine ⟨hbi,?_⟩
    intro k
    by_cases hki : k = i
    · simp only [hki,ite_true,mul_one]
    · have hk : a j*b k = 0 := by simpa only [hbj,mul_zero,add_zero,hki,Ne.symm hki,ite_false,zero_mul] using hcross k
      have hb := (mul_eq_zero.mp hk).resolve_left haj
      simp only [hb,hki,Ne.symm hki,ite_false,mul_zero]

end WaveTurbulence.VineEstS2

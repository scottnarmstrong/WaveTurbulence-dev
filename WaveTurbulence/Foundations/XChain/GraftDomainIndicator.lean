/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTimeDomain
public import WaveTurbulence.Foundations.XChain.GraftPhaseProducts
/-! Product indicators used in the grafted phase-integral factorization. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

theorem ite_and_forall_mul_prod {β : Type*} [Fintype β] {M : Type*} [CommMonoidWithZero M]
    (P : Prop) (Q : β → Prop) (a : M) (b : β → M) :
    (if P ∧ ∀ i, Q i then a * ∏ i, b i else 0) =
      (if P then a else 0) * ∏ i, if Q i then b i else 0 := by
  classical
  by_cases hp : P
  · by_cases hq : ∀ i, Q i
    · have he : (∏ i, if Q i then b i else 0) = ∏ i, b i :=
        Finset.prod_congr rfl (fun i _ => ite_eq_left (hq i))
      rw [ite_eq_left ⟨hp, hq⟩, ite_eq_left hp, he]
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hq
      have hz : (∏ j, if Q j then b j else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
      simp only [hp, hq, true_and, ite_false, ite_true, hz, mul_zero]
  · simp only [hp, false_and, ite_false, zero_mul]

end WaveTurbulence.Induct

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerFamilyKernelSum
/-! Group independent finite lower components by their exact orders before estimating. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_pi_fiber_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β γ : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)] [∀ i, DecidableEq (γ i)]
    (o : ∀ i, β i → γ i) (f : ∀ i, β i → ℂ) (n : ∀ i, γ i) :
    (∑ x : ∀ i, β i, if (fun i => o i (x i)) = n then ∏ i, f i (x i) else 0) =
      ∏ i, ∑ y : β i, if o i y = n i then f i y else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : (fun i => o i (x i)) = n
  · rw [if_pos hx]
    apply prod_congr rfl
    intro i _
    rw [if_pos (congrFun hx i)]
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ : ∃ i, o i (x i) ≠ n i := by
      by_contra! h
      exact hx (funext h)
    exact (prod_eq_zero (mem_univ i) (if_neg hi)).symm

theorem sum_pi_by_orders {ι : Type*} [Fintype ι] [DecidableEq ι] {β γ : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)] [∀ i, DecidableEq (γ i)]
    (o : ∀ i, β i → γ i) (f : ∀ i, β i → ℂ) (W : (∀ i, γ i) → ℂ) :
    (∑ x : ∀ i, β i, W (fun i => o i (x i)) * ∏ i, f i (x i)) =
      ∑ n : ∀ i, γ i, W n * ∏ i, ∑ y : β i, if o i y = n i then f i y else 0 := by
  classical
  have he := sum_fiberwise (univ : Finset (∀ i, β i)) (fun x i => o i (x i))
    (fun x => W (fun i => o i (x i)) * ∏ i, f i (x i))
  refine he.symm.trans ?_
  apply sum_congr rfl
  intro n _
  rw [← sum_pi_fiber_prod o f n, mul_sum]
  rw [sum_filter]
  apply sum_congr rfl
  intro x _
  split_ifs with hx
  · rw [hx]
  · simp

end WaveTurbulence.Induct

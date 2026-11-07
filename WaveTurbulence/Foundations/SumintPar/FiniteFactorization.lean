/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Factorization of finitely supported lattice sums

Compact input cutoffs reduce the lattice sums to an actual finite product
of finite sets. The identity is proved before absolute values are taken.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- A finite product of finitely supported complex factors is finitely supported. -/
theorem product_zero_outside_box {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    (s : ∀ i, Finset (α i)) (f : ∀ i, α i → ℂ)
    (hf : ∀ i x, x ∉ s i → f i x = 0) (x : ∀ i, α i)
    (hx : x ∉ Fintype.piFinset s) : (∏ i, f i (x i)) = 0 := by
  classical
  have hn : ¬ ∀ i, x i ∈ s i := fun h => hx (Fintype.mem_piFinset.mpr h)
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hf i (x i) hi)

/-- Literal factorization of the complex sum over all lattice variables. -/
theorem tsum_product_eq_product_tsum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    (s : ∀ i, Finset (α i)) (f : ∀ i, α i → ℂ)
    (hf : ∀ i x, x ∉ s i → f i x = 0) :
    (∑' x : ∀ i, α i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x := by
  classical
  rw [tsum_eq_sum (product_zero_outside_box s f hf), ← Finset.prod_univ_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (tsum_eq_sum (hf i)).symm

/-- Factorization is compatible with taking absolute values after each block sum. -/
theorem norm_tsum_product_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    (s : ∀ i, Finset (α i)) (f : ∀ i, α i → ℂ)
    (hf : ∀ i x, x ∉ s i → f i x = 0) :
    ‖∑' x : ∀ i, α i, ∏ i, f i (x i)‖ = ∏ i, ‖∑' x, f i x‖ := by
  rw [tsum_product_eq_product_tsum s f hf, norm_prod]

end WaveTurbulence.SumintPar

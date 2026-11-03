/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Tensorization of finitely supported lattice series -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- A finite product of finitely supported series is a series over the
product lattice. Finite support is explicit, so no conditional `tsum` is used. -/
theorem tsum_pi_prod_of_finite_support {ι : Type*} [Fintype ι]
    {α : ι → Type*} (f : ∀ i, α i → ℂ) (hf : ∀ i, (Function.support (f i)).Finite) :
    (∑' v : ∀ i, α i, ∏ i, f i (v i)) = ∏ i, ∑' a, f i a := by
  classical
  let S (i : ι) : Finset (α i) := (hf i).toFinset
  have hz (i : ι) (a : α i) (ha : a ∉ S i) : f i a = 0 := by
    by_contra h
    exact ha ((hf i).mem_toFinset.mpr h)
  calc
    _ = ∑ v ∈ Fintype.piFinset S, ∏ i, f i (v i) := by
      apply tsum_eq_sum
      intro v hv
      have hi : ∃ i, v i ∉ S i := by
        by_contra hh
        push Not at hh
        exact hv (Fintype.mem_piFinset.mpr hh)
      obtain ⟨i, hi⟩ := hi
      exact prod_eq_zero (mem_univ i) (hz i (v i) hi)
    _ = ∏ i, ∑ a ∈ S i, f i a := (prod_univ_sum S f).symm
    _ = _ := by
      apply prod_congr rfl
      intro i hi
      exact (tsum_eq_sum (fun a ha => hz i a ha)).symm

end WaveTurbulence.WeylSums

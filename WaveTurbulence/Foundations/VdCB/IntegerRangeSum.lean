/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Reindexing an actual consecutive integer block

The integer interval `(a,a+N]` is parametrized by the natural indices
`j<N`, through `a+j+1`. This is used to match A-process and Abel APIs.
-/

public section

namespace WaveTurbulence.VdCB

theorem sum_Ioc_int_eq_range {E : Type*} [AddCommMonoid E] (F : ℤ → E) (a : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc a (a + N), F n) = ∑ j ∈ Finset.range N, F (a + j + 1) := by
  have heq : Finset.Ioc a (a + N) = (Finset.range N).image (fun j : ℕ => a + j + 1) := by
    ext n
    constructor
    · intro hn
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
      apply Finset.mem_image.mpr
      refine ⟨(n - a - 1).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      have hJ := Finset.mem_range.mp hj
      apply Finset.mem_Ioc.mpr
      omega
  rw [heq, Finset.sum_image]
  intro i _ j _ hij
  dsimp only at hij
  omega

end WaveTurbulence.VdCB

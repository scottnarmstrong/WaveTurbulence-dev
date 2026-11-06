/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Complex.Basic
/-! Exact finite partition of a summable source decoration series, retaining all support conditions. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

theorem tsum_eq_sum_partition {X J : Type*} [Fintype J] (f : X → ℂ) (hf : Summable f)
    (P : J → X → Prop) (hpart : ∀ x, f x ≠ 0 → ∃! j, P j x) :
    (∑' x, f x) = ∑ j : J, ∑' x : {x // P j x}, f x.1 := by
  classical
  have hsum : ∀ j ∈ (univ : Finset J), Summable (fun x => if P j x then f x else 0) := by
    intro j _
    exact hf.indicator {x | P j x}
  have he (x : X) : f x = ∑ j : J, if P j x then f x else 0 := by
    by_cases hx : f x = 0
    · simp only [hx, ite_self, sum_const_zero]
    · obtain ⟨j, hj, huniq⟩ := hpart x hx
      rw [sum_eq_single j]
      · rw [if_pos hj]
      · intro i _ hij
        rw [if_neg (fun hi => hij (huniq i hi))]
      · intro h
        exact (h (mem_univ j)).elim
  calc
    _ = ∑' x, ∑ j : J, if P j x then f x else 0 := tsum_congr he
    _ = ∑ j : J, ∑' x, if P j x then f x else 0 := Summable.tsum_finsetSum hsum
    _ = _ := by
      apply sum_congr rfl
      intro j _
      exact (tsum_subtype (s := {x | P j x}) (f := f)).symm

end WaveTurbulence.LGSpine

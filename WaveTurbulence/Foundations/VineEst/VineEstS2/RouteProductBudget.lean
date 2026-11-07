/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Product budgets when every path vertex is charged at most twice -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- Double-count the finite incidence matrix of path segments. This is the
numerical step for replacing signed predecessors by subtraction-only ones. -/
theorem prod_route_cost_le_square {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (route : I → Finset J) (cost : J → ℕ) (hc : ∀ j, 1 ≤ cost j)
    (hcharge : ∀ j, (Finset.univ.filter (fun i => j ∈ route i)).card ≤ 2) :
    (∏ i, ∏ j ∈ route i, cost j) ≤ (∏ j, cost j)^2 := by
  classical
  have hf (i : I) : (∏ j ∈ route i, cost j) = ∏ j : J, if j ∈ route i then cost j else 1 := by
    rw [← Finset.prod_filter]
    apply Finset.prod_congr
    · ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    · intro j _
      rfl
  simp_rw [hf]
  rw [Finset.prod_comm]
  have hp (j : J) : (∏ i : I, if j ∈ route i then cost j else 1) =
      cost j ^ (Finset.univ.filter (fun i => j ∈ route i)).card := by
    rw [← Finset.prod_filter,Finset.prod_const]
  simp_rw [hp]
  calc
    _ ≤ ∏ j : J, cost j^2 := Finset.prod_le_prod (fun j _ => Nat.pow_le_pow_right (hc j) (hcharge j))
    _ = (∏ j : J, cost j)^2 := Finset.prod_pow _ _ _

end WaveTurbulence.VineEstS2

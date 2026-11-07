/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Tactic

/-!
# S2 REPRESENTS: the product of the slot mass bounds (real arithmetic)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents

theorem prod_slot_masses {ι : Type*} [Fintype ι] (m : ι → ℝ) (sz g : ι → ℕ) (K x L e : ℝ)
    (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hL : 0 < L)
    (hm : ∀ s, 0 ≤ m s ∧ m s ≤ K * x ^ (sz s) * L ^ (-e * (g s : ℝ))) :
    ∏ s, m s ≤ K ^ Fintype.card ι * x ^ (∑ s, sz s) * L ^ (-e * ((∑ s, g s : ℕ) : ℝ)) := by
  classical
  calc ∏ s, m s ≤ ∏ s, (K * x ^ (sz s) * L ^ (-e * (g s : ℝ))) :=
        Finset.prod_le_prod₀ (fun s _ => (hm s).1) (fun s _ => (hm s).2)
    _ = K ^ Fintype.card ι * x ^ (∑ s, sz s) * L ^ (-e * ((∑ s, g s : ℕ) : ℝ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Finset.prod_pow_eq_pow_sum]
        congr 1
        rw [← Real.rpow_sum_of_pos hL]
        congr 1
        push_cast
        rw [Finset.mul_sum]

end WaveTurbulence.Represents

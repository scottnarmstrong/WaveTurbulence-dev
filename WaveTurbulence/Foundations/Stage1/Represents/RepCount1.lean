/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm4
import Mathlib.Tactic

/-!
# S2 REPRESENTS: lattice points in a unit ball, and decorations with unit-ball supported bonds
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine

variable {w d : ℕ}

theorem ball_finset (L : ℝ) (hL : 0 < L) (a : Mom d) :
    ∃ F : Finset (Fin d → ℤ), F.card ≤ (⌊2 * L⌋₊ + 2) ^ d ∧
      ∀ n : Fin d → ℤ, ‖a + latticePoint L n‖ ≤ 1 → n ∈ F := by
  classical
  let lo : Fin d → ℤ := fun i => ⌈-L * (1 + a i)⌉
  let hi : Fin d → ℤ := fun i => ⌊L * (1 - a i)⌋
  refine ⟨Fintype.piFinset fun i => Finset.Icc (lo i) (hi i), ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    calc ∏ i, (Finset.Icc (lo i) (hi i)).card ≤ ∏ _i : Fin d, (⌊2 * L⌋₊ + 2) := by
          refine Finset.prod_le_prod fun i _ => ?_
          rw [Int.card_Icc]
          have h1 : (lo i : ℝ) ≥ -L * (1 + a i) := Int.le_ceil _
          have h2 : (hi i : ℝ) ≤ L * (1 - a i) := Int.floor_le _
          have h3 : ((hi i + 1 - lo i : ℤ) : ℝ) ≤ 2 * L + 1 := by
            push_cast; nlinarith
          have h4 : (((hi i + 1 - lo i).toNat : ℕ) : ℝ) ≤ 2 * L + 1 := by
            by_cases hn : 0 ≤ hi i + 1 - lo i
            · rw [show (((hi i + 1 - lo i).toNat : ℕ) : ℝ) = ((hi i + 1 - lo i : ℤ) : ℝ) by
                exact_mod_cast Int.toNat_of_nonneg hn]
              exact h3
            · rw [Int.toNat_of_nonpos (by omega)]
              simp; positivity
          have h5 : (hi i + 1 - lo i).toNat ≤ ⌊2 * L + 1⌋₊ := Nat.le_floor h4
          have h6 : ⌊2 * L + 1⌋₊ = ⌊2 * L⌋₊ + 1 := Nat.floor_add_one (by positivity)
          omega
      _ = (⌊2 * L⌋₊ + 2) ^ d := by simp
  · intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi' : |a i + (n i : ℝ) / L| ≤ 1 := by
      have := PiLp.norm_apply_le (a + latticePoint L n) i
      simpa [latticePoint, Real.norm_eq_abs] using this.trans hn
    rw [abs_le] at hi'
    constructor
    · refine Int.ceil_le.2 ?_
      have : -L ≤ L * a i + n i := by
        have := hi'.1
        have h2 : (n i : ℝ) / L = (n i : ℝ) * L⁻¹ := div_eq_mul_inv _ _
        have : -1 ≤ a i + (n i : ℝ) / L := hi'.1
        calc -L = L * (-1) := by ring
          _ ≤ L * (a i + (n i : ℝ) / L) := mul_le_mul_of_nonneg_left this hL.le
          _ = L * a i + n i := by field_simp
      linarith
    · refine Int.le_floor.2 ?_
      have : L * a i + n i ≤ L := by
        have : a i + (n i : ℝ) / L ≤ 1 := hi'.2
        calc L * a i + n i = L * (a i + (n i : ℝ) / L) := by field_simp
          _ ≤ L * 1 := mul_le_mul_of_nonneg_left this hL.le
          _ = L := by ring
      linarith

end WaveTurbulence.Represents

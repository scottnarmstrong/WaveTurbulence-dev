/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightTransfer
public import Mathlib.Algebra.BigOperators.Ring.Finset
/-! Exact finite expansion of the even root weights in TARGET L2065, preserving oscillatory sums. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

abbrev RootQuadraticChoice (ι : Type*) (d : ℕ) := Option (Fin d × ι × ι)

/-- Each quadratic choice is a signed product of two individual leaf coordinates, or the
constant 1. Its index is independent of every momentum decoration. -/
def rootQuadraticTerm {ι : Type*} {d : ℕ} (ε : ι → ℤˣ) (v : ι → Mom d) :
    RootQuadraticChoice ι d → ℝ
  | none => 1
  | some (j, a, b) => (((ε a : ℤ) : ℝ) * v a j) * (((ε b : ℤ) : ℝ) * v b j)

theorem sum_rootQuadraticTerm {ι : Type*} [Fintype ι] {d : ℕ}
    (ε : ι → ℤˣ) (v : ι → Mom d) :
    (∑ c : RootQuadraticChoice ι d, rootQuadraticTerm ε v c) =
      1 + ‖∑ i, (ε i : ℤ) • v i‖ ^ 2 := by
  classical
  rw [Fintype.sum_option]
  simp only [rootQuadraticTerm, Fintype.sum_prod_type]
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  apply sum_congr rfl
  intro j _
  have he : (∑ i, (ε i : ℤ) • v i) j = ∑ i, ((ε i : ℤ) : ℝ) * v i j := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, zsmul_eq_mul]
  rw [he, pow_two, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]

theorem jbr_sum_units_even_expansion {ι : Type*} [Fintype ι] {d : ℕ}
    (ε : ι → ℤˣ) (v : ι → Mom d) (m : ℕ) :
    jbr (∑ i, (ε i : ℤ) • v i) ^ (2 * m) =
      ∑ choice : Fin m → RootQuadraticChoice ι d,
        ∏ j, rootQuadraticTerm ε v (choice j) := by
  classical
  rw [pow_mul, jbr_sq, ← sum_rootQuadraticTerm ε v]
  have he := Fintype.prod_sum (fun _j : Fin m => rootQuadraticTerm ε v)
  simpa only [prod_const, card_univ, Fintype.card_fin] using he

theorem card_rootQuadraticChoice (ι : Type*) [Fintype ι] (d : ℕ) :
    Fintype.card (RootQuadraticChoice ι d) = 1 + d * Fintype.card ι * Fintype.card ι := by
  simp only [RootQuadraticChoice, Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Each root is expanded independently before the finite choices are distributed across leaves. -/
theorem root_weight_product_expansion {J : Type*} [Fintype J] [DecidableEq J]
    {ι : J → Type*} [∀ j, Fintype (ι j)] {d : ℕ}
    (ε : ∀ j, ι j → ℤˣ) (v : ∀ j, ι j → Mom d) (m : ℕ) :
    (∏ j, jbr (∑ i, (ε j i : ℤ) • v j i) ^ (2 * m)) =
      ∑ choice : ∀ j, Fin m → RootQuadraticChoice (ι j) d,
        ∏ j, ∏ a, rootQuadraticTerm (ε j) (v j) (choice j a) := by
  classical
  simp_rw [jbr_sum_units_even_expansion]
  exact Fintype.prod_sum _

/-- Exact size of the decoration-independent expansion index. -/
theorem card_root_weight_choices {J : Type*} [Fintype J] [DecidableEq J]
    (ι : J → Type*) [∀ j, Fintype (ι j)] (d m : ℕ) :
    Fintype.card (∀ j, Fin m → RootQuadraticChoice (ι j) d) =
      ∏ j, (1 + d * Fintype.card (ι j) * Fintype.card (ι j)) ^ m := by
  simp only [Fintype.card_pi, Fintype.card_fun, Fintype.card_fin, card_rootQuadraticChoice, prod_const, card_univ]

end WaveTurbulence.LGSpine

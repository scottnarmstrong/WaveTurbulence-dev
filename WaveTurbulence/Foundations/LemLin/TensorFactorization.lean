/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarFinite
public import Mathlib.Data.Fintype.BigOperators

/-!
# Tensor factorization of the linear cutoff sum

The tensor cutoff in TARGET `lemlin` lets one keep cancellation in a single
coordinate and bound all remaining scalar sums by `3L`.
-/

public section

namespace WaveTurbulence.LemLin
open Finset WithLp
open scoped Classical InnerProductSpace

private lemma char_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (Real.fourierChar (f i) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

private lemma linear_summand_eq_prod {d : ℕ} (L : ℝ) (a w : Mom d) (n : Fin d → ℤ) :
    Fourier.chi0TensorComplex (ofLp (latticePoint L n - a)) *
      (Real.fourierChar ⟪w, latticePoint L n⟫_ℝ : ℂ) =
      ∏ i, scalarAmplitude (a i) (-w i) ((n i : ℝ) / L) := by
  have hi : ⟪w, latticePoint L n⟫_ℝ = ∑ i, w i * ((n i : ℝ) / L) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, latticePoint]
    apply sum_congr rfl
    intro i _
    ring
  rw [hi, char_sum]
  simp only [Fourier.chi0TensorComplex, Fourier.chi0Tensor, Complex.ofReal_prod,
    ← prod_mul_distrib, scalarAmplitude, Fourier.chi0Complex, neg_neg]
  rfl

/-- TARGET `lemlin`: factor the vector lattice sum into scalar cutoff sums. -/
theorem linearLatticeSum_eq_prod {d : ℕ} {L : ℝ} (hL : 0 < L) (a w : Mom d) :
    linearLatticeSum L a w = ∏ i, scalarLatticeSum L (a i) (-w i) := by
  rw [linearLatticeSum_eq_sum hL]
  simp_rw [linear_summand_eq_prod]
  change (∑ n ∈ Fintype.piFinset (fun i => scalarIndexSet L (a i)),
      ∏ i, scalarAmplitude (a i) (-w i) ((n i : ℝ) / L)) = _
  rw [← prod_univ_sum (fun i => scalarIndexSet L (a i))
    (fun i (n : ℤ) => scalarAmplitude (a i) (-w i) ((n : ℝ) / L))]
  apply prod_congr rfl
  intro i _
  exact (scalarLatticeSum_eq_sum hL (a i) (-w i)).symm

/-- Keep the oscillation in one coordinate and bound the other factors trivially. -/
theorem norm_linearLatticeSum_le_coordinate {d : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (a w : Mom d) (i : Fin d) :
    ‖linearLatticeSum L a w‖ ≤ (3 * L) ^ (d - 1) * ‖scalarLatticeSum L (a i) (-w i)‖ := by
  rw [linearLatticeSum_eq_prod (by linarith), norm_prod,
    ← prod_erase_mul _ _ (mem_univ i)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ∏ _j ∈ (univ : Finset (Fin d)).erase i, (3 * L) :=
      prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_scalarLatticeSum_le hL _ _)
    _ = _ := by simp

end WaveTurbulence.LemLin

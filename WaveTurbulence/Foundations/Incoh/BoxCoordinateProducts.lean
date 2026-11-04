/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BoxIntegralLinearity
public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra

/-!
# Coordinate products in the recursive box integral

These factorization identities let first-variation bounds tensorize in
all selected clocks without differentiating a rectangular indicator.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual box integral of independent coordinate factors is their product mass. -/
theorem boxIntegral_coordinate_product (n : ℕ) {f : Fin n → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ⊤) (R : ℝ) :
    Fourier.boxIntegral n (fun v => ∏ i, f i (v i)) R = ∏ i, ∫⁻ x in Icc (-R) R, f i x := by
  induction n with
  | zero => simp only [Fourier.boxIntegral, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
    change (∫⁻ x in Icc (-R) R,
      Fourier.boxIntegral n (fun v => ∏ i : Fin (n + 1), f i ((Fin.cons x v : Fin (n + 1) → ℝ) i)) R) = _
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hc (x : ℝ) := Fourier.boxIntegral_const_mul n (f 0 x) (hfin 0 x)
      (fun v => ∏ i : Fin n, f i.succ (v i)) R
    simp_rw [hc]
    have ht := ih (fun i => hf i.succ) (fun i x => hfin i.succ x)
    rw [ht, lintegral_mul_const _ (hf 0)]

/-- Box integration distributes over finite measurable sums. -/
theorem boxIntegral_finset_sum {ι : Type*} (n : ℕ) (s : Finset ι)
    {f : ι → (Fin n → ℝ) → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i)) (R : ℝ) :
    Fourier.boxIntegral n (fun v => ∑ i ∈ s, f i v) R = ∑ i ∈ s, Fourier.boxIntegral n (f i) R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Fourier.boxIntegral_const, mul_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [Fourier.boxIntegral_add n (hf i (Finset.mem_insert_self _ _)) _ R,
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end WaveTurbulence.Incoh

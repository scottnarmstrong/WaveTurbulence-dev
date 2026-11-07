/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InputCutoffInsertion
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-!
# Uniform finite lattice support of the inserted input cutoffs

The source cutoff at scale four leaves at most `(8L+1)^(dM)` input
lattice points. This gives absolute convergence for every localized
Fourier summand before any oscillatory cancellation is used.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The inserted cutoff is nonnegative. -/
theorem inputCutoff_nonneg {d : ℕ} (a : Fin d → ℝ) (x : Mom d) : 0 ≤ inputCutoff a x :=
  Fourier.chi0Tensor_nonneg _

/-- The inserted cutoff is at most one. -/
theorem inputCutoff_le_one {d : ℕ} (a : Fin d → ℝ) (x : Mom d) : inputCutoff a x ≤ 1 :=
  Fourier.chi0Tensor_le_one _

/-- Nonzero input cutoffs have a literal fixed finite integer-coordinate box. -/
theorem inputCutoff_mem_integerBox {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a : Fin d → ℝ) (n : Fin d → ℤ) (hn : inputCutoff a (latticePoint L n) ≠ 0) :
    n ∈ Counting.latticeBox (fun j => L*a j) (4*L) := by
  classical
  apply (Counting.mem_latticeBox _ _ _).mpr
  intro j
  have hc : |((n j : ℝ)/L-a j)/4| < 1 := by
    by_contra hh
    apply hn
    exact Fourier.chi0Tensor_eq_zero j (not_lt.mp hh)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hc
  have hc' : |(n j : ℝ)/L-a j| < 4 := by
    simpa only [one_mul] using (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hc
  have he : (n j : ℝ)-L*a j = L*((n j : ℝ)/L-a j) := by field_simp
  rw [he, abs_mul, abs_of_pos hL]
  exact (mul_lt_mul_of_pos_left hc' hL).le.trans_eq (by ring)

/-- The fixed integer rectangle containing all input cutoff support. -/
@[expose] noncomputable def inputCutoffBox {ι : Type*} [Fintype ι] {d : ℕ}
    (L : ℝ) (a : ι → Fin d → ℝ) : Finset (ι → Fin d → ℤ) := by
  classical
  exact Fintype.piFinset (fun i => Counting.latticeBox (fun j => L*a i j) (4*L))

/-- Outside the rectangle, at least one input cutoff vanishes. -/
theorem inputCutoff_product_eq_zero {ι : Type*} [Fintype ι] {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a : ι → Fin d → ℝ) (x : ι → Fin d → ℤ) (hx : x ∉ inputCutoffBox L a) :
    (∏ i, inputCutoff (a i) (latticePoint L (x i))) = 0 := by
  classical
  have hh : ¬ ∀ i, x i ∈ Counting.latticeBox (fun j => L*a i j) (4*L) := by
    intro hh
    exact hx (Fintype.mem_piFinset.mpr hh)
  push Not at hh
  obtain ⟨i, hi⟩ := hh
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_contra hn
  exact hi (inputCutoff_mem_integerBox hL (a i) (x i) hn)

/-- Cardinality of the actual finite support rectangle. -/
theorem card_inputCutoffBox_le {ι : Type*} [Fintype ι] {d : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (a : ι → Fin d → ℝ) : ((inputCutoffBox L a).card : ℝ) ≤ (8*L+1)^(d*Fintype.card ι) := by
  classical
  rw [inputCutoffBox, Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : ι, (8*L+1)^d := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro i _
      have hc := Counting.card_latticeBox_le (fun j => L*a i j) (by positivity : 0 ≤ 4*L)
      simpa only [show 2*(4*L)+1 = 8*L+1 by ring] using hc
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]

/-- Every localized Fourier lattice summand is genuinely summable, independently of its phase. -/
theorem summable_inputCutoff_mul {ι : Type*} [Fintype ι] {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a : ι → Fin d → ℝ) (F : (ι → Fin d → ℤ) → ℂ) :
    Summable (fun x => ((∏ i, inputCutoff (a i) (latticePoint L (x i)) : ℝ) : ℂ) * F x) := by
  classical
  apply summable_of_ne_finset_zero (s := inputCutoffBox L a)
  intro x hx
  rw [inputCutoff_product_eq_zero hL a x hx, Complex.ofReal_zero, zero_mul]

end WaveTurbulence.SumintPar

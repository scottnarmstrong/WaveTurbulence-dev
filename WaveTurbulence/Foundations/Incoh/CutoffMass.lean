/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LinkFactor
public import WaveTurbulence.Foundations.WeylSums.TranslatedCutoffMass

/-!
# Uniform lattice mass of the localized link cutoffs

TARGET (incohproof12): tensorize the landed scalar bound `5L`; do not
introduce any dependence on the real cutoff centers.
-/

public section

noncomputable section

open Finset

namespace WaveTurbulence.Incoh

variable {d : ℕ}

theorem latticeCutoff_nonneg (x : Mom d) : 0 ≤ WeylSums.latticeCutoff x :=
  prod_nonneg fun _ _ => Fourier.chi0_nonneg _

theorem latticeCutoff_le_one (x : Mom d) : WeylSums.latticeCutoff x ≤ 1 := by
  calc
    _ ≤ ∏ _i : Fin d, (1 : ℝ) := prod_le_prod₀
      (fun i _ => Fourier.chi0_nonneg (x i)) (fun i _ => Fourier.chi0_le_one (x i))
    _ = 1 := by simp only [prod_const_one]

/-- The actual vector cutoff mass is the product of the one-dimensional masses. -/
theorem tsum_latticeCutoff_eq_prod {L : ℝ} (hL : 0 < L) (a : Mom d) :
    (∑' n : Fin d → ℤ, WeylSums.latticeCutoff (latticePoint L n - a)) =
      ∏ i : Fin d, ∑' m : ℤ, Fourier.chi0 ((m : ℝ) / L - a i) := by
  have hf (i : Fin d) : (Function.support (fun m : ℤ =>
      (Fourier.chi0 ((m : ℝ) / L - a i) : ℂ))).Finite := by
    simpa only [Function.support, ne_eq, Complex.ofReal_eq_zero] using WeylSums.finite_scalar_cutoff hL (a i)
  have H := WeylSums.tsum_pi_prod_of_finite_support
    (fun i (m : ℤ) => (Fourier.chi0 ((m : ℝ) / L - a i) : ℂ)) hf
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_tsum, Complex.ofReal_prod]
  convert H using 1
  apply tsum_congr
  intro n
  simp only [WeylSums.latticeCutoff, latticePoint, PiLp.sub_apply, Complex.ofReal_prod]

/-- Explicit, center-independent vector lattice mass bound. -/
theorem tsum_latticeCutoff_le {L : ℝ} (hL : 1 ≤ L) (a : Mom d) :
    (∑' n : Fin d → ℤ, WeylSums.latticeCutoff (latticePoint L n - a)) ≤ (5 * L) ^ d := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [tsum_latticeCutoff_eq_prod hLp]
  calc
    _ ≤ ∏ _i : Fin d, (5 * L) := prod_le_prod₀
      (fun i _ => tsum_nonneg fun _ => Fourier.chi0_nonneg _)
      (fun i _ => WeylSums.tsum_translated_chi0_le hL (a i))
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]

end WaveTurbulence.Incoh

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # F61 sign transport in the regular-couple asymptotics

DH23 (KQZapprox), DH21 Prop7.5, and corrected TARGET (regref1-3).
The positive special prefactors and the extracted coefficient sign combine
to exactly the negative inverse product used in B2.
-/

public section
namespace WaveTurbulence.RegAsymp
open Finset

/-- Extracting one minus sign per special variable gives the corrected
B2 special weight. No nonvanishing assumption on the factors is needed. -/
theorem prod_neg_inv_eq_sign_mul {ι : Type*} (Z : Finset ι) (f : ι → ℂ) :
    (∏ z ∈ Z, (-f z)⁻¹) = (-1 : ℂ) ^ Z.card * ∏ z ∈ Z, (f z)⁻¹ := by
  simp only [inv_neg,prod_neg]

/-- The sign remains inside the coefficient until the final assembly.
DH21 Prop7.5 corrected by F61: integral coefficient =(-1)^|Z| JB. -/
theorem special_coefficient_sign {ι : Type*} (Z : Finset ι) (f : ι → ℂ) (JB M : ℂ) :
    (∏ z ∈ Z, (f z)⁻¹) * ((-1 : ℂ)^Z.card * JB) * M =
      (∏ z ∈ Z, (-f z)⁻¹) * JB * M := by
  rw [prod_neg_inv_eq_sign_mul]
  ring

end WaveTurbulence.RegAsymp

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.AffineCharacter

/-!
# The source pi-normalized phase as an additive character

The source writes exp(pi*i*theta), whereas the Fourier transform uses
2*pi. Keeping the source phase as a genuine additive character makes
its finite product identities exact, with the half-frequency conversion
explicit only when the landed lattice sums are invoked.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The literal pi-normalized complex phase in TARGET sumint. -/
@[expose] noncomputable def piCharacter : AddChar ℝ ℂ where
  toFun θ := Complex.exp ((Real.pi*θ : ℝ)*Complex.I)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The source phase has unit modulus. -/
theorem norm_piCharacter (θ : ℝ) : ‖piCharacter θ‖ = 1 := by
  simp [piCharacter,Complex.norm_exp]

/-- The source phase is continuous. -/
theorem continuous_piCharacter : Continuous piCharacter := by
  change Continuous (fun θ : ℝ => Complex.exp ((Real.pi*θ : ℝ)*Complex.I))
  fun_prop

/-- Exact conversion to the canonical Fourier character. -/
theorem piCharacter_eq_fourierChar_half (θ : ℝ) :
    piCharacter θ = (Real.fourierChar (θ/2) : ℂ) := by
  rw [Real.fourierChar_apply]
  change Complex.exp ((Real.pi*θ : ℝ)*Complex.I) = _
  congr 1
  push_cast
  ring

/-- Exact reverse conversion from the canonical Fourier normalization. -/
theorem fourierChar_eq_piCharacter_double (θ : ℝ) :
    (Real.fourierChar θ : ℂ) = piCharacter (2*θ) := by
  rw [piCharacter_eq_fourierChar_half]
  apply congrArg (fun s : ℝ => (Real.fourierChar s : ℂ))
  ring

/-- The finite-sum law of the source character. -/
theorem piCharacter_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    piCharacter (∑ i ∈ s, f i) = ∏ i ∈ s, piCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

/-- The independent 2pi input modulation in source pi phase notation. -/
theorem inputCharacter_eq_piCharacter {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) :
    inputCharacter D L ν x = piCharacter (2*∑ v, inner ℝ (ν v) (latticePoint L (x v))) := by
  unfold inputCharacter
  rw [prod_fourierChar_eq_sum,piCharacter_eq_fourierChar_half]
  apply congrArg (fun s : ℝ => (Real.fourierChar s : ℂ))
  ring

end WaveTurbulence.SumintPar

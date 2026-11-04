/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.AffineModulation
public import WaveTurbulence.Foundations.Sumint.CutoffPhaseSum

/-!
# Exact affine character separation in the localized weight expansion

The transposed affine matrices produce the independent input character.
The remaining external character is independent of time and has unit
modulus, so the proved output-multiplier estimate applies without loss.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- A finite product of complex Fourier characters is the character of the sum. -/
theorem prod_fourierChar_eq_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, (Real.fourierChar (f i) : ℂ)) = (Real.fourierChar (∑ i ∈ s, f i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,AddChar.map_add_eq_mul]
    rfl

/-- The product of source affine characters separates literally into input
and external characters. -/
theorem source_affine_character_eq {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d)
    (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) :
    (∏ i, (Real.fourierChar (inner ℝ (ξ i)
      (Sum.elim (D.kVec L x E) (D.ℓVec L x E) i)) : ℂ)) =
      inputCharacter D L (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) x *
        (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E) : ℂ) := by
  rw [prod_fourierChar_eq_sum, Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [affine_modulation_identity,AddChar.map_add_eq_mul]
  unfold inputCharacter
  rw [prod_fourierChar_eq_sum]
  rfl

/-- The external source character has unit modulus uniformly in the output momenta. -/
theorem norm_source_external_character {d : ℕ} (D : SumintDatum d)
    (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) (E : Fin 4 → Mom d) :
    ‖(Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E) : ℂ)‖ = 1 :=
  Circle.norm_coe _

end WaveTurbulence.Sumint

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PhaseExponent

/-!
# Exact scalar-amplitude and character form of the source phase

All source phase factors are retained. The lattice-independent factor can
be separated by subtracting its real exponent, without ever dividing by
the case-(c) amplitude, which may be zero.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The first source factor is its scalar amplitude times the character of
its literal real exponent. -/
theorem firstPhaseFactor_eq_character {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) :
    firstPhaseFactor D L γ δ η x r t τ i =
      caseCFactor D η τ i*piCharacter (firstPhaseExponent D L γ δ x r t τ i) := by
  unfold firstPhaseFactor firstPhaseExponent
  simp only [AddChar.map_add_eq_mul,piCharacter_sum]
  ac_rfl

/-- The normal source factor is exactly the character of its complete exponent. -/
theorem normalPhaseFactor_eq_character {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) :
    normalPhaseFactor D L γ δ x r t τ i = piCharacter (normalPhaseExponent D L γ δ x r t τ i) := by
  unfold normalPhaseFactor normalPhaseExponent
  simp only [AddChar.map_add_eq_mul,piCharacter_sum]

/-- The literal source phase is its scalar amplitude times a single additive character. -/
theorem phase_eq_amplitude_character {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    D.phase L γ δ η x r t τ = caseCAmplitude D η τ*piCharacter (fullPhaseExponent D L γ δ x r t τ) := by
  rw [phase_eq_factor_products]
  simp_rw [firstPhaseFactor_eq_character,normalPhaseFactor_eq_character]
  rw [Finset.prod_mul_distrib]
  unfold caseCAmplitude fullPhaseExponent
  rw [AddChar.map_add_eq_mul,piCharacter_sum,piCharacter_sum]
  ac_rfl

/-- Separate the zero-input source phase without division or nonvanishing assumptions. -/
theorem phase_eq_zero_mul_exponent_difference {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    D.phase L γ δ η x r t τ = D.phase L γ δ η (fun _ => 0) r t τ *
      piCharacter (fullPhaseExponent D L γ δ x r t τ -
        fullPhaseExponent D L γ δ (fun _ => 0) r t τ) := by
  rw [phase_eq_amplitude_character,phase_eq_amplitude_character,mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

end WaveTurbulence.SumintPar

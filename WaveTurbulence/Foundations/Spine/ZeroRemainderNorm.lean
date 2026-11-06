/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpatialNormFromWords
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
/-! The zero remainder satisfies every spatial input bound, at every order. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open NormBridgeScratch
open scoped ENNReal

theorem wordD_zero_function {d : ℕ} (word : List (Fin d)) :
    wordD word (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    simp only [wordD, ih]
    funext x
    simp [partialMom]

 theorem SNorm_zero_function {d : ℕ} (A B : ℕ) : SNorm A B (fun _ : Mom d => (0 : ℂ)) = 0 := by
  apply le_antisymm _ bot_le
  apply SNorm_le_of_word_enorm_bounds _ contDiff_const
  intro word _ x
  rw [wordD_zero_function]
  simp

 theorem inputRemainder_zero (P : WTParams) (r : ℕ) :
    InputRemainder P (fun _ => 0) r := by
  unfold InputRemainder SNormR
  simp only [Complex.ofReal_zero, SNorm_zero_function]
  exact bot_le

end WaveTurbulence.LGSpine

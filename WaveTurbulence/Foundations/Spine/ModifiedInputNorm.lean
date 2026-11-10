/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateMonomialNorm
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeNorm
public import WaveTurbulence.Foundations.Sumint.MultiIndices
public import WaveTurbulence.Foundations.XChain.SNormRealPart
/-! The explicit individually weighted and differentiated source inputs have finite low-order norms. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset NormBridgeScratch

theorem coordinateWord_eq_ofReal {d : ℕ} (word : List (Fin d)) (x : Mom d) :
    coordinateWord word x = (((word.map (fun j => x j)).prod : ℝ) : ℂ) := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    change (x j : ℂ) * coordinateWord word x = _
    rw [ih, List.map_cons, List.prod_cons, Complex.ofReal_mul]

end WaveTurbulence.LGSpine

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AffineDerivativeWords

/-!
# Square-free coordinate derivatives inside the actual weighted jet family
-/

public section

noncomputable section

open scoped SchwartzMap LineDeriv

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Coordinate indices selected by a square-free derivative, in its actual composition order. -/
@[expose] def selectedCoordinates : (n : ℕ) → (Fin n → Bool) → List (Fin n)
  | 0, _ => []
  | n + 1, b => (selectedCoordinates n (Fin.tail b)).map Fin.succ ++ if b 0 then [0] else []

/-- A square-free derivative uses at most one letter per coordinate. -/
theorem length_selectedCoordinates_le : ∀ (n : ℕ) (b : Fin n → Bool),
    (selectedCoordinates n b).length ≤ n
  | 0, _ => by simp only [selectedCoordinates, List.length_nil, le_refl]
  | n + 1, b => by
      have H := length_selectedCoordinates_le n (Fin.tail b)
      simp only [selectedCoordinates, List.length_append, List.length_map]
      split <;> simp only [List.length_singleton, List.length_nil] <;> omega

/-- Selected affine directions are precisely the selected coordinate columns. -/
theorem selectedDirections_eq_map : ∀ {n : ℕ} (b : Fin n → Bool) (V : Fin n → Mom d),
    selectedDirections b V = (selectedCoordinates n b).map V
  | 0, _, _ => rfl
  | n + 1, b, V => by
      rw [selectedDirections, selectedCoordinates, List.map_append, List.map_map,
        selectedDirections_eq_map]
      rw [Fin.tail_def]
      cases b 0 <;> simp [Function.comp_def]

/-- Directional coordinate words are exactly the derivative letters of the weighted jet. -/
theorem derivativeWordCLM_basis (w : List (Fin d)) (f : 𝓢(Mom d, ℝ)) :
    derivativeWordCLM (w.map (fun i => EuclideanSpace.single i (1 : ℝ))) f =
      jetWordCLM (w.map Sum.inr) f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [List.map_cons, derivativeWordCLM, jetWordCLM, jetLetterCLM,
        ContinuousLinearMap.comp_apply, ih]

/-- The standard affine coordinate map is the actual Euclidean-space coordinate equivalence. -/
theorem affineCoordinatePoint_basis (x : Fin d → ℝ) :
    affineCoordinatePoint 0 (fun i => EuclideanSpace.single i (1 : ℝ)) x =
      (WithLp.toLp 2 x : Mom d) := by
  have H : (WithLp.toLp 2 x : Mom d) = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (WithLp.toLp 2 x)]
    simp
  simpa only [affineCoordinatePoint, zero_add] using H.symm

/-- Actual coordinate mixed partials are members of the finite weighted Schwartz jet family. -/
theorem mixedPartial_toLp_schwartz (b : Fin d → Bool) (f : 𝓢(Mom d, ℝ)) (x : Fin d → ℝ) :
    Analysis.mixedPartial d b (fun y => f (WithLp.toLp 2 y)) x =
      jetWordCLM ((selectedCoordinates d b).map Sum.inr) f (WithLp.toLp 2 x) := by
  simpa only [affineCoordinatePoint_basis, selectedDirections_eq_map, derivativeWordCLM_basis] using
    mixedPartial_affine_schwartz b (fun i => EuclideanSpace.single i (1 : ℝ)) f 0 x

end WaveTurbulence.WKEL2

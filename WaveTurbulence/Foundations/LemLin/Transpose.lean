/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Transposing finite blocks of physical coordinates

Changing from spatial-coordinate-first to vector-first indexing preserves
product Lebesgue measure. This gives the paper's vector notation for the
cubic estimate without changing its integral.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set

private theorem uncurry_measurePreserving (n m : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin m) ℝ).symm := by
  let e := (MeasurableEquiv.curry (Fin n) (Fin m) ℝ).symm
  refine ⟨e.measurable, ?_⟩
  change Measure.map e volume = Measure.pi (fun _ : Fin n × Fin m => (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [e.map_apply]
  have he : e ⁻¹' (univ.pi s) = univ.pi (fun i : Fin n => univ.pi (fun j : Fin m => s (i, j))) := by
    ext x
    simp [e, MeasurableEquiv.coe_curry_symm, Function.uncurry_def, Prod.forall]
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun p : Fin n × Fin m => volume (s p))).symm

/-- Transpose a finite rectangular array of physical coordinates. -/
@[expose] def transposeCoordinates (n m : ℕ) :
    (Fin n → Fin m → ℝ) ≃ᵐ (Fin m → Fin n → ℝ) :=
  (MeasurableEquiv.curry (Fin n) (Fin m) ℝ).symm |>.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin m × Fin n => ℝ)
      (Equiv.prodComm (Fin n) (Fin m))).trans (MeasurableEquiv.curry (Fin m) (Fin n) ℝ))

@[simp] theorem transposeCoordinates_apply (n m : ℕ) (p : Fin n → Fin m → ℝ)
    (j : Fin m) (i : Fin n) : transposeCoordinates n m p j i = p i j := rfl

/-- The physical coordinate transpose preserves standard product volume. -/
theorem transposeCoordinates_measurePreserving (n m : ℕ) :
    MeasurePreserving (transposeCoordinates n m) :=
  (uncurry_measurePreserving n m).trans
    ((measurePreserving_piCongrLeft (fun _ : Fin m × Fin n => (volume : Measure ℝ))
      (Equiv.prodComm (Fin n) (Fin m))).trans
        ((uncurry_measurePreserving m n).symm _))

end WaveTurbulence.LemLin

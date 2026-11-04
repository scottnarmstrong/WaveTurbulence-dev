/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TripleFrequencyCoordinates
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Exact volume-preserving symmetries of native exit frequencies

Coordinate exchanges and reflection of the first frequency are used
only to align the scalar one-exit kernel pairing with its source phase.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- Exchange the first native frequency with another specified native coordinate. -/
@[expose] noncomputable def frequencySwapFirst (j : Fin 3) : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.swap 0 j)

/-- Every native coordinate exchange preserves volume. -/
theorem volume_preserving_frequencySwapFirst (j : Fin 3) :
    MeasurePreserving (frequencySwapFirst j) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℝ) (Equiv.swap 0 j)

/-- The first-second native exchange has its literal coordinate action. -/
theorem frequencySwapFirst_one_apply (ξ : Fin 3 → ℝ) : frequencySwapFirst 1 ξ = ![ξ 1,ξ 0,ξ 2] := by
  funext j
  fin_cases j <;> rfl

/-- The first-third native exchange has its literal coordinate action. -/
theorem frequencySwapFirst_two_apply (ξ : Fin 3 → ℝ) : frequencySwapFirst 2 ξ = ![ξ 2,ξ 1,ξ 0] := by
  funext j
  fin_cases j <;> rfl

/-- Reflect only the first native exit frequency. -/
@[expose] noncomputable def frequencyReflectFirst : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  tripleFrequencyEquiv.trans ((MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ)
    (MeasurableEquiv.refl (ℝ × ℝ))).trans tripleFrequencyEquiv.symm)

/-- Reflection of the first exit frequency preserves native volume. -/
theorem volume_preserving_frequencyReflectFirst : MeasurePreserving frequencyReflectFirst volume volume := by
  have hp : MeasurePreserving (fun q : ℝ × (ℝ × ℝ) => (-q.1,q.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (show MeasurePreserving (id : ℝ × ℝ → ℝ × ℝ) volume volume from ⟨measurable_id,Measure.map_id⟩)
  exact (MeasurePreserving.symm tripleFrequencyEquiv volume_preserving_tripleFrequencyEquiv).comp
    (hp.comp volume_preserving_tripleFrequencyEquiv)

/-- The first-frequency reflection has its literal coordinate action. -/
theorem frequencyReflectFirst_apply (ξ : Fin 3 → ℝ) : frequencyReflectFirst ξ = ![-ξ 0,ξ 1,ξ 2] := rfl

end WaveTurbulence.Sumint

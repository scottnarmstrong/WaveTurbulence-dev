/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SelectedCoordinateSplit
public import WaveTurbulence.Foundations.Fourier.TimeFourier

/-!
# Native marginals on selected input-time coordinates

The unchanged complement is integrated out using the exact
measure-preserving coordinate split. Integrability and measurability
are inherited from the full input coefficient. The selected-coordinate
character agrees pointwise with the ordinary coordinate Fourier phase.
-/

public section

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Integrate out every unselected input coordinate, without changing the selected order. -/
@[expose] noncomputable def selectedCoordinateMarginal {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (x : Fin r → ℝ) : ℂ :=
  ∫ y : {i : ι // i ∉ Set.range v} → ℝ, f ((selectedCoordinateSplit v hv).symm (x,y))

/-- The sparse native Fourier character on an injective selected-coordinate list. -/
@[expose] noncomputable def selectedCoordinateCharacter {ι : Type*} {r : ℕ}
    (v : Fin r → ι) (ξ : Fin r → ℝ) (u : ι → ℝ) : ℂ :=
  Real.fourierChar (-∑ j, u (v j)*ξ j)

/-- The native coefficient after coordinate separation is genuinely integrable. -/
theorem integrable_selectedCoordinateSplit_symm {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (hf : Integrable f) :
    Integrable (fun z : (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ) =>
      f ((selectedCoordinateSplit v hv).symm z)) := by
  have hp := MeasurePreserving.symm (selectedCoordinateSplit v hv) (volume_preserving_selectedCoordinateSplit v hv)
  exact (hp.integrable_comp_emb (selectedCoordinateSplit v hv).symm.measurableEmbedding).mpr hf

/-- Integrating out the unselected coordinates preserves genuine integrability. -/
theorem integrable_selectedCoordinateMarginal {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (hf : Integrable f) :
    Integrable (selectedCoordinateMarginal v hv f) := by
  have hi := integrable_selectedCoordinateSplit_symm v hv f hf
  rw [Measure.volume_eq_prod] at hi
  exact hi.integral_prod_left

/-- A measurable full coefficient gives a measurable selected-coordinate marginal. -/
theorem measurable_selectedCoordinateMarginal {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (hf : Measurable f) :
    Measurable (selectedCoordinateMarginal v hv f) :=
  ((hf.comp (selectedCoordinateSplit v hv).symm.measurable).stronglyMeasurable.integral_prod_right').measurable

/-- After the split, the sparse native character is exactly the ordinary coordinate Fourier character. -/
theorem selectedCoordinateCharacter_split_symm {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (ξ : Fin r → ℝ)
    (z : (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ)) :
    selectedCoordinateCharacter v ξ ((selectedCoordinateSplit v hv).symm z) =
      (Real.fourierChar (-Fourier.timePairing r z.1 ξ):ℂ) := by
  unfold selectedCoordinateCharacter Fourier.timePairing
  change (Real.fourierChar (-∑ j, ((selectedCoordinateSplit v hv).symm z) (v j)*ξ j):ℂ) =
    (Real.fourierChar (-∑ j, z.1 j*ξ j):ℂ)
  simp_rw [selectedCoordinateSplit_symm_selected]

/-- The selected-coordinate Fourier character has unit norm. -/
theorem norm_selectedCoordinateCharacter {ι : Type*} {r : ℕ}
    (v : Fin r → ι) (ξ : Fin r → ℝ) (u : ι → ℝ) : ‖selectedCoordinateCharacter v ξ u‖ = 1 :=
  Circle.norm_coe _

end WaveTurbulence.Sumint

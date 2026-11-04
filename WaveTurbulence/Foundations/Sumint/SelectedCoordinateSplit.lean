/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measure-preserving separation of selected input coordinates

An injective list of r coordinates is separated from its unchanged
complement. The selected coordinates are placed in Fin r order, so the
one- and two-exit amplitudes use the ordinary coordinate Fourier transform.
No source carrier is replaced or quotiented.
-/

public section

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Separate an injective finite list of coordinates from all unselected coordinates. -/
@[expose] noncomputable def selectedCoordinateSplit {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) :
    (ι → ℝ) ≃ᵐ (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => i ∈ Set.range v)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : {i : ι // i ∈ Set.range v} => ℝ) (Equiv.ofInjective v hv)).symm
      (MeasurableEquiv.refl _))

/-- The selected-coordinate separation preserves the actual product Lebesgue measure. -/
theorem volume_preserving_selectedCoordinateSplit {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) :
    MeasurePreserving (selectedCoordinateSplit v hv) volume volume := by
  let : Fintype {i : ι // i ∈ Set.range v} := Subtype.fintype (fun i => i ∈ Set.range v)
  let e := MeasurableEquiv.piCongrLeft (fun _ : {i : ι // i ∈ Set.range v} => ℝ) (Equiv.ofInjective v hv)
  have he : MeasurePreserving e volume volume := volume_measurePreserving_piCongrLeft _ _
  have hei : MeasurePreserving e.symm volume volume := MeasurePreserving.symm e he
  have hid : MeasurePreserving (id : ({i : ι // i ∉ Set.range v} → ℝ) → _) volume volume :=
    ⟨measurable_id,Measure.map_id⟩
  have hp : MeasurePreserving (MeasurableEquiv.prodCongr e.symm (MeasurableEquiv.refl ({i : ι // i ∉ Set.range v} → ℝ))) volume volume := by
    rw [Measure.volume_eq_prod]
    exact hei.prod hid
  exact hp.comp (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => i ∈ Set.range v))

/-- The forward selected coordinates are exactly the coordinates of the original input vector. -/
theorem selectedCoordinateSplit_selected {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (u : ι → ℝ) (j : Fin r) :
    (selectedCoordinateSplit v hv u).1 j = u (v j) := rfl

/-- The inverse separation restores each selected coordinate at its original source index. -/
theorem selectedCoordinateSplit_symm_selected {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v)
    (x : (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ)) (j : Fin r) :
    ((selectedCoordinateSplit v hv).symm x) (v j) = x.1 j := by
  have hh := selectedCoordinateSplit_selected v hv ((selectedCoordinateSplit v hv).symm x) j
  rw [MeasurableEquiv.apply_symm_apply] at hh
  exact hh.symm

end WaveTurbulence.Sumint

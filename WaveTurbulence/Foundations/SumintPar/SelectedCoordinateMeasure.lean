/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SelectedCoordinateSplit
public import WaveTurbulence.Foundations.SumintPar.FixedCoordinateMeasure

/-!
# Selected-coordinate separation for arbitrary native product measures

The selected-coordinate permutation preserves the product of any
sigma-finite native coordinate measures, including mixed Dirac/Lebesgue
measures. This identifies the remaining-coordinate integral with the
full native product integral at the prescribed selected values.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Selected-coordinate separation preserves arbitrary sigma-finite native product measures. -/
theorem measurePreserving_selectedCoordinateSplit {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (selectedCoordinateSplit v hv) (Measure.pi μ)
      ((Measure.pi fun j => μ (v j)).prod (Measure.pi fun i : {i : ι // i ∉ Set.range v} => μ i.1)) := by
  let : Fintype {i : ι // i ∈ Set.range v} := Subtype.fintype (fun i => i ∈ Set.range v)
  let e := MeasurableEquiv.piCongrLeft (fun _ : {i : ι // i ∈ Set.range v} => ℝ) (Equiv.ofInjective v hv)
  have he : MeasurePreserving e (Measure.pi fun j => μ (v j))
      (Measure.pi fun i : {i : ι // i ∈ Set.range v} => μ i.1) :=
    measurePreserving_piCongrLeft (fun i : {i : ι // i ∈ Set.range v} => μ i.1) (Equiv.ofInjective v hv)
  have hei := MeasurePreserving.symm e he
  have hid : MeasurePreserving (id : ({i : ι // i ∉ Set.range v} → ℝ) → _)
      (Measure.pi fun i : {i : ι // i ∉ Set.range v} => μ i.1)
      (Measure.pi fun i : {i : ι // i ∉ Set.range v} => μ i.1) := ⟨measurable_id,Measure.map_id⟩
  exact (hei.prod hid).comp (measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ Set.range v))

end WaveTurbulence.SumintPar

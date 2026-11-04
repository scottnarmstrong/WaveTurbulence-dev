/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SelectedCoordinateMeasure
public import WaveTurbulence.Foundations.Sumint.PiDiracReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The remaining-coordinate trace is a full native fixed/free product integral

The injective selected-coordinate list fixes exactly its prescribed
values. All unselected coordinates retain Lebesgue measure. The formula
is exact for every nonnegative measurable coefficient and every choice
of the selected values; no almost-everywhere selection is used.
-/

public section

open MeasureTheory ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The native vector extending selected values by zero on their unchanged complement. -/
@[expose] noncomputable def selectedFixedVector {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (x : Fin r → ℝ) : ι → ℝ :=
  (selectedCoordinateSplit v hv).symm (x,fun _ => 0)

/-- The full mixed-coordinate integral equals exactly the native remaining-coordinate trace. -/
theorem lintegral_fixedCoordinateTrace_eq {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (x : Fin r → ℝ)
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, f u ∂Measure.pi (fixedCoordinateMeasure (Set.range v) (selectedFixedVector v hv x))) =
      ∫⁻ y : {i : ι // i ∉ Set.range v} → ℝ, f ((selectedCoordinateSplit v hv).symm (x,y)) := by
  let μ := fixedCoordinateMeasure (Set.range v) (selectedFixedVector v hv x)
  have hsel (j : Fin r) : μ (v j) = Measure.dirac (x j) := by
    dsimp [μ,fixedCoordinateMeasure,selectedFixedVector]
    rw [ite_eq_left (Set.mem_range_self j),selectedCoordinateSplit_symm_selected]
  have hrest (i : {i : ι // i ∉ Set.range v}) : μ i.1 = volume := by
    dsimp [μ,fixedCoordinateMeasure]
    rw [ite_eq_right i.2]
  have hselPi : (Measure.pi fun j => μ (v j)) = Measure.dirac x := by
    simp_rw [hsel]
    exact pi_dirac_real_eq x
  have hrestPi : (Measure.pi fun i : {i : ι // i ∉ Set.range v} => μ i.1) = volume := by
    simp_rw [hrest]
    rfl
  have hp := measurePreserving_selectedCoordinateSplit v hv μ
  rw [hselPi,hrestPi] at hp
  have he := hp.lintegral_comp_emb (selectedCoordinateSplit v hv).measurableEmbedding
    (fun z => f ((selectedCoordinateSplit v hv).symm z))
  simp only [MeasurableEquiv.symm_apply_apply] at he
  rw [he]
  have hm : Measurable (fun z : (Fin r → ℝ) × ({i : ι // i ∉ Set.range v} → ℝ) =>
      f ((selectedCoordinateSplit v hv).symm z)) := hf.comp (selectedCoordinateSplit v hv).symm.measurable
  have hFub := lintegral_prod (μ := Measure.dirac x) (ν := (volume : Measure ({i : ι // i ∉ Set.range v} → ℝ)))
    (fun z => f ((selectedCoordinateSplit v hv).symm z)) hm.aemeasurable
  exact hFub.trans (lintegral_dirac x _)

end WaveTurbulence.Sumint

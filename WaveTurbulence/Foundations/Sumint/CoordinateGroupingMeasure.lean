/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ProductMeasureTools

/-!
# Regrouping arbitrary coordinate product measures

The same coordinate permutations used for Lebesgue time integration
also preserve arbitrary sigma-finite coordinate measures. In particular,
selected times can carry Dirac measures while all remaining times carry
Lebesgue measure, without changing the source coordinate carrier.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- An exact coordinate permutation followed by currying preserves every sigma-finite product measure. -/
theorem measurePreserving_coordinateGrouping {ι B : Type*} [Fintype ι] [Fintype B]
    {C : B → Type*} [∀ b, Fintype (C b)] (e : (Σ b : B, C b) ≃ ι)
    (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : (Σ b : B, C b) => ℝ) e.symm).trans
        (MeasurableEquiv.piCurry (fun (b : B) (_ : C b) => ℝ)))
      (Measure.pi μ) (Measure.pi fun b => Measure.pi fun j => μ (e ⟨b,j⟩)) := by
  have hr := measurePreserving_piCongrLeft (fun z : (Σ b : B, C b) => μ (e z)) e.symm
  have hr' : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : (Σ b : B, C b) => ℝ) e.symm)
      (Measure.pi μ) (Measure.pi fun z => μ (e z)) := by
    simpa only [Equiv.apply_symm_apply] using hr
  exact (measurePreserving_piCurry (fun (b : B) (_ : C b) => ℝ) (fun b j => μ (e ⟨b,j⟩))).comp hr'

end WaveTurbulence.Sumint

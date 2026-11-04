/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantSymmetry
public import WaveTurbulence.Foundations.WKEL2.ResonantIntegral

/-!
# Signed symmetry of the resonant integral
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Signed integrability is preserved by the resonant swap. -/
theorem integrable_resonant_swap {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ} (hF : Integrable F (resonantMeasure e)) :
    Integrable (fun p => F (p.2, p.1)) (resonantMeasure e) := by
  have hMP : MeasurePreserving (MeasurableEquiv.prodComm (α := Mom d) (β := Mom d))
      (resonantMeasure e) (resonantMeasure e) :=
    ⟨measurable_swap, map_swap_resonantMeasure he hd⟩
  exact (hMP.integrable_comp_emb (MeasurableEquiv.prodComm (α := Mom d) (β := Mom d)).measurableEmbedding).mpr hF

/-- Signed delta-integral symmetry follows from the nonnegative measure symmetry. -/
theorem deltaInt_swap_of_integrable {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ} (hF : Integrable F (resonantMeasure e)) :
    deltaInt (fun a b => F (b, a)) = deltaInt (fun a b => F (a, b)) := by
  have hMP : MeasurePreserving (MeasurableEquiv.prodComm (α := Mom d) (β := Mom d))
      (resonantMeasure e) (resonantMeasure e) :=
    ⟨measurable_swap, map_swap_resonantMeasure he hd⟩
  have hi := integrable_resonant_swap he hd hF
  have h := hMP.integral_comp' (f := MeasurableEquiv.prodComm (α := Mom d) (β := Mom d)) F
  change (∫ p, F (p.2, p.1) ∂resonantMeasure e) = ∫ p, F p ∂resonantMeasure e at h
  rw [integral_resonantMeasure_eq_two_deltaInt he hi,
    integral_resonantMeasure_eq_two_deltaInt he hF] at h
  linarith only [h]

end WaveTurbulence.WKEL2

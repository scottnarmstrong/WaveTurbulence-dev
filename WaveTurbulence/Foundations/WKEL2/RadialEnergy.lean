/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedL2
public import WaveTurbulence.Foundations.WKEL2.Polar
public import WaveTurbulence.Foundations.WKEL2.PolarDensityPower

/-!
# Nonnegative radial masses and energies

These extended integrals retain exceptional infinite ray energies until
angular integration; no pointwise ray integrability is assumed.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Absolute ray mass in the resonant radial density. -/
@[expose] def radialMass (f : Mom d → ℝ) (k v : Mom d) : ℝ≥0∞ :=
  ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal |f (k + r.1 • v)| ∂Measure.volumeIoiPow (d - 2)

/-- Weighted L² energy on a ray, equal to the square of Γ in the research note. -/
@[expose] def radialEnergy (s : ℝ) (f : Mom d → ℝ) (k v : Mom d) : ℝ≥0∞ :=
  ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal ((weightedFunction s f (k + r.1 • v)) ^ 2)
    ∂Measure.volumeIoiPow (d - 1)

/-- Measurability of ray mass in the direction. -/
theorem measurable_radialMass {f : Mom d → ℝ} (hf : Measurable f) (k : Mom d) :
    Measurable (radialMass f k) := by
  have hc : Continuous (fun p : Mom d × Ioi (0 : ℝ) => k + p.2.1 • p.1) := by fun_prop
  exact (hf.abs.ennreal_ofReal.comp hc.measurable).lintegral_prod_right'

/-- Measurability of ray energy in the direction. -/
theorem measurable_radialEnergy (s : ℝ) {f : Mom d → ℝ} (hf : Measurable f) (k : Mom d) :
    Measurable (radialEnergy s f k) := by
  have hc : Continuous (fun p : Mom d × Ioi (0 : ℝ) => k + p.2.1 • p.1) := by fun_prop
  exact (((measurable_weightedFunction s hf).pow_const 2).ennreal_ofReal.comp hc.measurable).lintegral_prod_right'

/-- Angular integration of radial energy is the exact frozen weighted norm squared. -/
theorem lintegral_radialEnergy (hd : 0 < d) (s : ℝ) {f : Mom d → ℝ}
    (hf : Measurable f) (hLp : MemLp (weightedFunction s f) 2) (k : Mom d) :
    (∫⁻ v : sphere (0 : Mom d) 1, radialEnergy s f k v.1
      ∂(volume : Measure (Mom d)).toSphere) = ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  have hG : Measurable (fun x : Mom d => ENNReal.ofReal ((weightedFunction s f x) ^ 2)) :=
    ((measurable_weightedFunction s hf).pow_const 2).ennreal_ofReal
  have hshift : Measurable (fun u : Mom d =>
      ENNReal.ofReal ((weightedFunction s f (k + u)) ^ 2)) :=
    hG.comp (continuous_const.add continuous_id).measurable
  have hp := lintegral_polar volume hshift
  rw [finrank_euclideanSpace_fin] at hp
  calc
    _ = ∫⁻ u : Mom d, ENNReal.ofReal ((weightedFunction s f (k + u)) ^ 2) := hp.symm
    _ = ∫⁻ x : Mom d, ENNReal.ofReal ((weightedFunction s f x) ^ 2) :=
      lintegral_add_left_eq_self (fun x => ENNReal.ofReal ((weightedFunction s f x) ^ 2)) k
    _ = _ := (ofReal_weightedL2Norm_sq s f hLp).symm

end WaveTurbulence.WKEL2

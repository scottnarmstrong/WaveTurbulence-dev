/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularM2
public import WaveTurbulence.Foundations.WKEL2.RadialEnergy

/-!
# Weighted angular Schur integral

The bound pairing ray energy in one angular variable with A_k in the other,
used in research-note Proposition 5.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- A_k is measurable as a function of direction, with its center fixed. -/
theorem measurable_radialWeight_direction (s : ℝ) (k : Mom d) :
    Measurable (fun v : Mom d => radialWeight d s k v) := by
  have hb : Continuous (fun q : Mom d × ℝ => 1 + ‖k + q.2 • q.1‖ ^ 2) := by fun_prop
  have hc : Continuous (fun q : Mom d × ℝ =>
      (1 + ‖k + q.2 • q.1‖ ^ 2) ^ (-s) * q.2 ^ (d - 3)) :=
    (hb.rpow_const (fun _ => Or.inl (by positivity))).mul (continuous_snd.pow _)
  exact hc.stronglyMeasurable.integral_prod_right.measurable

/-- The angular Schur energy bound, with one constant for all inputs and centers. -/
theorem exists_angular_schur_energy_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ f : Mom d → ℝ,
      Measurable f → MemLp (weightedFunction s f) 2 → ∀ k : Mom d,
        (∫⁻ p, radialEnergy s f k p.1 * ENNReal.ofReal (radialWeight d s k p.2)
          ∂angularMeasure e) ≤ ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_reference_M2 hd s hs
  refine ⟨C, hC, fun e he f hf hLp k => ?_⟩
  have hE := measurable_radialEnergy s hf k
  have hA := (measurable_radialWeight_direction s k).ennreal_ofReal
  have hG : Measurable (fun p : Mom d × Mom d =>
      radialEnergy s f k p.1 * ENNReal.ofReal (radialWeight d s k p.2)) :=
    (hE.comp measurable_fst).mul (hA.comp measurable_snd)
  rw [lintegral_angularMeasure he (by omega) hG]
  have hinner (φ : sphere (0 : Mom d) 1) :
      (∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1, radialEnergy s f k φ.1 *
        ENNReal.ofReal (radialWeight d s k (normalReflection e φ.1 θ.1))
          ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere) ≤
        radialEnergy s f k φ.1 * ENNReal.ofReal C := by
    have hm : Measurable (fun θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1 =>
        ENNReal.ofReal (radialWeight d s k (normalReflection e φ.1 θ.1))) :=
      hA.comp ((normalReflection e φ.1).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)).measurable
    rw [lintegral_const_mul _ hm]
    exact mul_le_mul' le_rfl (hbound e he φ.1 (mem_sphere_zero_iff_norm.mp φ.2) k)
  calc
    _ ≤ ∫⁻ φ : sphere (0 : Mom d) 1, radialEnergy s f k φ.1 * ENNReal.ofReal C
        ∂(volume : Measure (Mom d)).toSphere := lintegral_mono hinner
    _ = ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
      have hEs : Measurable (fun φ : sphere (0 : Mom d) 1 => radialEnergy s f k φ.1) :=
        hE.comp measurable_subtype_coe
      rw [lintegral_mul_const _ hEs,
        lintegral_radialEnergy (by omega) s hf hLp k, mul_comm]

end WaveTurbulence.WKEL2

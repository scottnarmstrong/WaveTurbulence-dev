/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.MaskedModulation

/-! # Joint tensor measurability for arbitrary actual masked modulations -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh
open scoped ContDiff

/-- Integer-center choices need only measurability. All momentum
derivatives are of the actual masked amplitude; scalar parameters need
no smoothness, and the derivative-tensor codomain needs no Borel instance. -/
theorem stronglyMeasurable_derivative_maskedModulation {d m : ℕ} {U : Type*}
    [MeasurableSpace U] (c : U → Fin m → Fin d → ℤ) (hc : Measurable c)
    (a : U → ℂ) (ha : StronglyMeasurable a) (v : U → Mom d) (hv : StronglyMeasurable v)
    (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun q => iteratedFDeriv ℝ j (maskedModulation (c q) (a q) (v q)) k) := by
  have hjoint : StronglyMeasurable (fun p : (Fin m → Fin d → ℤ) × (ℂ × Mom d) =>
      iteratedFDeriv ℝ j (maskedModulation p.1 p.2.1 p.2.2) k) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (c : Fin m → Fin d → ℤ) (q : ℂ × Mom d) =>
        iteratedFDeriv ℝ j (maskedModulation c q.1 q.2) k)
    · intro q
      exact continuous_of_discreteTopology
    · intro c
      have hcont : Continuous (fun q : ℂ × Mom d =>
          iteratedFDeriv ℝ j (maskedModulation c q.1 q.2) k) :=
        continuous_iteratedFDeriv_smooth_modulated (sourceRootMask c) (contDiff_sourceRootMask c)
          (fun q : ℂ × Mom d => q.1) continuous_fst (fun q : ℂ × Mom d => q.2) continuous_snd k j
      exact hcont.stronglyMeasurable
  have hp : Measurable (fun q => (c q,(a q,v q))) := hc.prodMk (ha.measurable.prodMk hv.measurable)
  exact hjoint.comp_measurable (g := fun q : U => (c q,(a q,v q))) hp

/-- The scalar common derivative envelope is jointly measurable for the
same arbitrary center, amplitude, and frequency data. -/
theorem measurable_maskedModulation_envelope {d m : ℕ} {U : Type*} [MeasurableSpace U]
    (N W : ℕ) (c : U → Fin m → Fin d → ℤ) (hc : Measurable c)
    (a : U → ℂ) (ha : StronglyMeasurable a) (v : U → Mom d) (hv : StronglyMeasurable v) :
    Measurable (fun q => maskedSourceSpatialConstant d m N W *
      (∏ i, Fourier.momentumBracket (NTSP.intVec (c q i))^W)*(1+‖v q‖)^N*‖a q‖) := by
  have hcenter : Measurable (fun c : Fin m → Fin d → ℤ =>
      ∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W) := measurable_of_countable _
  exact (((measurable_const.mul (hcenter.comp hc)).mul
    ((measurable_const.add hv.measurable.norm).pow_const N)).mul ha.measurable.norm)

end WaveTurbulence.RegAsymp

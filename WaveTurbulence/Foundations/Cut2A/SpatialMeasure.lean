/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cut2A.Chirp
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasureDefs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Tactic
/-! Integrable Fourier-measure presentations and closure; C2-A NOTES §3.1. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Cut2A
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable (α : Type*) [MeasurableSpace α]

variable {V α}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [BorelSpace V] [SecondCountableTopology V] in
theorem SpatialMeasure.mass_nonneg (F : SpatialMeasure V α) : 0 ≤ F.mass :=
  integral_nonneg fun _ => norm_nonneg _

theorem SpatialMeasure.integrable_character (F : SpatialMeasure V α) (x : V) :
    Integrable (fun a => F.amplitude a * (Real.fourierChar (inner ℝ (F.frequency a) x) : ℂ)) F.μ := by
  have hm : Measurable (fun a => (Real.fourierChar (inner ℝ (F.frequency a) x) : ℂ)) :=
    character_smooth.continuous.measurable.comp
      (F.frequency_measurable.inner measurable_const)
  apply F.amplitude_integrable.norm.mono' (F.amplitude_integrable.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    change ‖F.amplitude a * (Real.fourierChar (inner ℝ (F.frequency a) x) : ℂ)‖ ≤ ‖F.amplitude a‖
    simp only [norm_mul, Circle.norm_coe, mul_one, le_refl]

omit [BorelSpace V] [SecondCountableTopology V] in
theorem SpatialMeasure.norm_value_le (F : SpatialMeasure V α) (x : V) : ‖F.value x‖ ≤ F.mass := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp [SpatialMeasure.mass]

variable {β : Type*} [MeasurableSpace β]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [CompleteSpace V] [CompleteSpace W]

/-- Pullback by any continuous affine map, including rank-deficient conservation maps. -/
def SpatialMeasure.affine (F : SpatialMeasure V α) (A : W →L[ℝ] V) (b : V) : SpatialMeasure W α where
  μ := F.μ
  sigmaFinite := inferInstance
  frequency := fun a => A.adjoint (F.frequency a)
  frequency_measurable := A.adjoint.continuous.measurable.comp F.frequency_measurable
  amplitude := fun a => F.amplitude a * (Real.fourierChar (inner ℝ (F.frequency a) b) : ℂ)
  amplitude_integrable := F.integrable_character b

theorem SpatialMeasure.affine_value (F : SpatialMeasure V α) (A : W →L[ℝ] V) (b : V) (x : W) :
    (F.affine A b).value x = F.value (A x + b) := by
  simp only [SpatialMeasure.value, SpatialMeasure.affine, A.adjoint_inner_left,
    inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by ring
end WaveTurbulence.Cut2A

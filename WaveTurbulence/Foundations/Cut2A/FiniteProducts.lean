/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasure
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
/-! Finite products of spatial Fourier measures with explicit multiplicative mass, C2-A. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
namespace WaveTurbulence.Cut2A
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- All factors may have distinct parameter spaces. -/
def SpatialMeasure.finiteProduct (F : (i : ι) → SpatialMeasure V (α i))
    [∀ i, SigmaFinite (F i).μ] : SpatialMeasure V ((i : ι) → α i) where
  μ := Measure.pi (fun i => (F i).μ)
  sigmaFinite := inferInstance
  frequency := fun a => ∑ i, (F i).frequency (a i)
  frequency_measurable := by
    exact Finset.measurable_sum _ fun i _ => (F i).frequency_measurable.comp (measurable_pi_apply i)
  amplitude := fun a => ∏ i, (F i).amplitude (a i)
  amplitude_integrable := Integrable.fintype_prod_dep (fun i => (F i).amplitude_integrable)

omit [InnerProductSpace ℝ V] in
theorem SpatialMeasure.finiteProduct_mass (F : (i : ι) → SpatialMeasure V (α i))
    [∀ i, SigmaFinite (F i).μ] : (SpatialMeasure.finiteProduct F).mass = ∏ i, (F i).mass := by
  simp only [SpatialMeasure.mass, SpatialMeasure.finiteProduct, norm_prod]
  exact integral_fintype_prod_eq_prod (fun i a => ‖(F i).amplitude a‖)

theorem SpatialMeasure.finiteProduct_value (F : (i : ι) → SpatialMeasure V (α i))
    [∀ i, SigmaFinite (F i).μ] (x : V) :
    (SpatialMeasure.finiteProduct F).value x = ∏ i, (F i).value x := by
  have hchar (a : (i : ι) → α i) (s : Finset ι) :
      (Real.fourierChar (∑ i ∈ s, inner ℝ ((F i).frequency (a i)) x) : ℂ) =
        ∏ i ∈ s, (Real.fourierChar (inner ℝ ((F i).frequency (a i)) x) : ℂ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp only [sum_empty, AddChar.map_zero_eq_one, Circle.coe_one, prod_empty]
    | @insert i s hi ih =>
      rw [sum_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, prod_insert hi, ih]
  simp only [SpatialMeasure.value, SpatialMeasure.finiteProduct, sum_inner]
  simp_rw [hchar, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun i => (F i).μ) (fun i a =>
    (F i).amplitude a * (Real.fourierChar (inner ℝ ((F i).frequency a) x) : ℂ))

omit [InnerProductSpace ℝ V] in
/-- Explicit product bound, with no loss from the number or size of affine coefficients. -/
theorem SpatialMeasure.finiteProduct_mass_le (F : (i : ι) → SpatialMeasure V (α i))
    [∀ i, SigmaFinite (F i).μ] (B : ι → ℝ) (hB : ∀ i, (F i).mass ≤ B i) :
    (SpatialMeasure.finiteProduct F).mass ≤ ∏ i, B i := by
  rw [SpatialMeasure.finiteProduct_mass]
  exact prod_le_prod₀ (fun i _ => (F i).mass_nonneg) (fun i _ => hB i)
end WaveTurbulence.Cut2A

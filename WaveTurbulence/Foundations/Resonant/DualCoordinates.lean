/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.LocalDerivatives
public import WaveTurbulence.Foundations.WKE.Multilinear

/-!
# Integrating finite-dimensional derivative functionals

A continuous linear functional is the finite sum of its values on a basis
times the corresponding coordinate functionals. Measurability and integrability
can therefore be checked on those scalar coefficients. This avoids assuming
measurability of a moving-hyperplane derivative integral.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Resonant

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {ι : Type*} [Fintype ι]

/-- A coordinate functional associated with a finite basis. -/
@[expose] noncomputable def basisCoordCLM (b : Module.Basis ι ℝ H) (i : ι) : H →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap

/-- Reconstruction of a functional from its finitely many basis evaluations. -/
theorem clm_eq_sum_basisCoord (b : Module.Basis ι ℝ H) (T : H →L[ℝ] ℝ) :
    T = ∑ i, (T (b i)) • basisCoordCLM b i := by
  classical
  ext x
  have h := congrArg T (b.sum_equivFun x)
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  rw [← h]
  simp only [sum_apply, smul_apply, basisCoordCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Scalar basis coefficients suffice for strong measurability of a dual-valued map. -/
theorem aestronglyMeasurable_clm_of_basis
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (b : Module.Basis ι ℝ H)
    {T : α → H →L[ℝ] ℝ}
    (h : ∀ i, AEStronglyMeasurable (fun a => T a (b i)) μ) :
    AEStronglyMeasurable T μ := by
  classical
  have hh : AEStronglyMeasurable (fun a => ∑ i, T a (b i) • basisCoordCLM b i) μ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => (h i).smul_const _)
  exact hh.congr (Filter.Eventually.of_forall fun a => (clm_eq_sum_basisCoord b (T a)).symm)

/-- Scalar integrability of the basis coefficients gives dual-valued integrability. -/
theorem integrable_clm_of_basis
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (b : Module.Basis ι ℝ H)
    {T : α → H →L[ℝ] ℝ} (h : ∀ i, Integrable (fun a => T a (b i)) μ) :
    Integrable T μ := by
  classical
  have hh : Integrable (fun a => ∑ i, T a (b i) • basisCoordCLM b i) μ :=
    integrable_finsetSum (f := fun i a => T a (b i) • basisCoordCLM b i)
      Finset.univ (fun i _ => (h i).smul_const (basisCoordCLM b i))
  exact hh.congr (Filter.Eventually.of_forall fun a => (clm_eq_sum_basisCoord b (T a)).symm)

end WaveTurbulence.Resonant

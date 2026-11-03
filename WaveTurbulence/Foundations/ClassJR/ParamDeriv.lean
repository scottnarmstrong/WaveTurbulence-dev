/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Iterated derivatives with a measurable parameter

The symbols of DH21 §5.2 are functions `m(α, γ)`, smooth in `α` and merely measurable in `γ`.
This module supplies the two analytic facts about such functions that the class `J`/`R` calculus
uses:

* `stronglyMeasurable_iteratedFDeriv_param`, `stronglyMeasurable_uncurry_iteratedFDeriv_param`:
  if `m(·, γ)` is smooth for every `γ` and `m(α, ·)` is measurable for every `α`, then every
  iterated `α`-derivative is measurable in `γ`, and jointly measurable in `(α, γ)`
  (difference quotients and a Carathéodory argument);
* `iteratedFDeriv_integral_param`: differentiation under the integral sign to every order, under
  a uniform-in-`α` integrable domination of each derivative.
-/

public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace WaveTurbulence.ClassJR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {Z : Type*} [MeasurableSpace Z]

/-- A map into continuous linear maps on a finite-dimensional space is strongly measurable as soon
as all its evaluations are. -/
theorem stronglyMeasurable_clm_of_apply {φ : Z → E →L[ℝ] G}
    (h : ∀ v, StronglyMeasurable fun z => φ z v) : StronglyMeasurable φ := by
  classical
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → StrongDual ℝ E := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  have hrepr : φ = fun z => ∑ i, ContinuousLinearMap.smulRightL ℝ E G (c i) (φ z (b i)) := by
    funext z
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRightL_apply_apply, c]
    calc φ z v = φ z (∑ i, b.repr v i • b i) := by rw [b.sum_repr v]
      _ = _ := by rw [map_sum]; simp only [map_smul]; rfl
  rw [hrepr]
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ E G (c i)).continuous.comp_stronglyMeasurable (h (b i))

/-- The derivative in `e` of a function `g(e, z)` that is differentiable in `e` and measurable in
`z` is measurable in `z`. -/
theorem stronglyMeasurable_fderiv_param {g : E → Z → G} (hd : ∀ z, Differentiable ℝ (g · z))
    (hm : ∀ e, StronglyMeasurable (g e)) (e : E) :
    StronglyMeasurable fun z => fderiv ℝ (g · z) e := by
  refine stronglyMeasurable_clm_of_apply fun v => ?_
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hlim : Tendsto (fun (n : ℕ) (z : Z) =>
      ((n : ℝ) + 1) • (g (e + ((n : ℝ) + 1)⁻¹ • v) z - g e z)) atTop
      (𝓝 fun z => fderiv ℝ (g · z) e v) := by
    rw [tendsto_pi_nhds]
    intro z
    exact ((hd z) e).hasFDerivAt.lim v hc
  exact stronglyMeasurable_of_tendsto atTop
    (fun n => ((hm _).sub (hm e)).const_smul _) hlim

/-- All iterated derivatives in `e` of a function smooth in `e` and measurable in `z` are
measurable in `z`. -/
theorem stronglyMeasurable_iteratedFDeriv_param {f : E → Z → G}
    (hf : ∀ z, ContDiff ℝ ∞ (f · z)) (hm : ∀ e, StronglyMeasurable (f e)) (k : ℕ) (e : E) :
    StronglyMeasurable fun z => iteratedFDeriv ℝ k (f · z) e := by
  induction k generalizing e with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E G).symm.continuous.comp_stronglyMeasurable (hm e)
  | succ k ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    refine (LinearIsometryEquiv.continuous _).comp_stronglyMeasurable
      (stronglyMeasurable_fderiv_param (g := fun e z => iteratedFDeriv ℝ k (f · z) e)
        (fun z => (hf z).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top k)) ih e)

/-- Joint measurability of the iterated derivatives (Carathéodory). -/
theorem stronglyMeasurable_uncurry_iteratedFDeriv_param [MeasurableSpace E] [BorelSpace E]
    {f : E → Z → G}
    (hf : ∀ z, ContDiff ℝ ∞ (f · z)) (hm : ∀ e, StronglyMeasurable (f e)) (k : ℕ) :
    StronglyMeasurable fun p : E × Z => iteratedFDeriv ℝ k (f · p.2) p.1 :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun e z => iteratedFDeriv ℝ k (f · z) e)
    (fun z => (hf z).continuous_iteratedFDeriv (mod_cast le_top))
    (stronglyMeasurable_iteratedFDeriv_param hf hm k)

section Integral

variable [CompleteSpace G] {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
/-- One step of differentiation under the integral sign for the `k`-th derivative. -/
theorem hasFDerivAt_integral_iteratedFDeriv_param {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ ∞ (f · x))
    (hm : ∀ k e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) (k : ℕ) (e : E) :
    HasFDerivAt (fun e => ∫ x, iteratedFDeriv ℝ k (f · x) e ∂μ)
      (∫ x, fderiv ℝ (fun e => iteratedFDeriv ℝ k (f · x) e) e ∂μ) e := by
  obtain ⟨B, hBi, hB⟩ := hb (k + 1)
  obtain ⟨B₀, hB₀i, hB₀⟩ := hb k
  have hdiff : ∀ x, Differentiable ℝ (fun e => iteratedFDeriv ℝ k (f · x) e) := fun x =>
    (hf x).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top k)
  have hm' : AEStronglyMeasurable
      (fun x => fderiv ℝ (fun e => iteratedFDeriv ℝ k (f · x) e) e) μ := by
    have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E)
      G).continuous.comp_aestronglyMeasurable (hm (k + 1) e)
    exact this
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ) (bound := B)
    Filter.univ_mem (Eventually.of_forall fun e' => hm k e')
    (hB₀i.mono' (hm k e) (by filter_upwards [hB₀] with x hx using hx e)) hm'
    (by filter_upwards [hB] with x hx e' _; rw [norm_fderiv_iteratedFDeriv]; exact hx e')
    hBi (Eventually.of_forall fun x e' _ => (hdiff x e').hasFDerivAt)

omit [FiniteDimensional ℝ E] in
/-- **Differentiation under the integral sign to every order.** If `f(e, x)` is smooth in `e`,
each iterated derivative is measurable in `x`, and each iterated derivative is dominated uniformly
in `e` by an integrable function of `x`, then the iterated derivatives of `e ↦ ∫ f(e, x) dx` are
the integrals of the iterated derivatives. -/
theorem iteratedFDeriv_integral_param {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ ∞ (f · x))
    (hm : ∀ k e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) (k : ℕ) :
    iteratedFDeriv ℝ k (fun e => ∫ x, f e x ∂μ) =
      fun e => ∫ x, iteratedFDeriv ℝ k (f · x) e ∂μ := by
  induction k with
  | zero =>
    funext e
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry.integral_comp_comm
      _).symm
  | succ k ih =>
    funext e
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih,
      (hasFDerivAt_integral_iteratedFDeriv_param hf hm hb k e).fderiv]
    exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) G)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) G).symm.toLinearIsometry
      _).symm

omit [FiniteDimensional ℝ E] in
/-- The parametric integral of a dominated smooth family is smooth. -/
theorem contDiff_integral_param {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ ∞ (f · x))
    (hm : ∀ k e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) :
    ContDiff ℝ ∞ (fun e => ∫ x, f e x ∂μ) := by
  refine contDiff_of_differentiable_iteratedFDeriv fun k _ => ?_
  rw [iteratedFDeriv_integral_param hf hm hb k]
  exact fun e => (hasFDerivAt_integral_iteratedFDeriv_param hf hm hb k e).differentiableAt

end Integral

end WaveTurbulence.ClassJR

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.ParamDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Differentiation under the integral sign to a finite order

The finite-order version of the landed `ClassJR.ParamDeriv` (which is stated for `C^∞` families): if `f(e, x)` is
`C^N` in `e` for every `x`, measurable in `x`, and each iterated derivative of order `≤ N` is dominated uniformly in
`e` by an integrable function of `x` (almost everywhere), then `e ↦ ∫ f(e, x) dx` is `C^N` and its iterated
derivatives of order `≤ N` are the integrals of the iterated derivatives.

Also `norm_le_sum_coordWords`: a multilinear map on `(ℝ^d)^n` is bounded by the sum of its values on coordinate
words (used to dominate `‖D^n f‖` by the coordinate derivatives of TARGET (normX)).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace WaveTurbulence.Regref

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {Z : Type*} [MeasurableSpace Z]

/-- Iterated derivatives of order `≤ N` of a family `C^N` in `e` and measurable in `z` are measurable in `z`. -/
theorem stronglyMeasurable_iteratedFDeriv_param_of_le {N : ℕ} {f : E → Z → G}
    (hf : ∀ z, ContDiff ℝ N (f · z)) (hm : ∀ e, StronglyMeasurable (f e)) :
    ∀ k : ℕ, k ≤ N → ∀ e, StronglyMeasurable fun z => iteratedFDeriv ℝ k (f · z) e
  | 0, _, e => by
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E G).symm.continuous.comp_stronglyMeasurable (hm e)
  | k + 1, hk, e => by
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    refine (LinearIsometryEquiv.continuous _).comp_stronglyMeasurable
      (ClassJR.stronglyMeasurable_fderiv_param (g := fun e z => iteratedFDeriv ℝ k (f · z) e)
        (fun z => (hf z).differentiable_iteratedFDeriv (by exact_mod_cast (show k < N by omega)))
        (stronglyMeasurable_iteratedFDeriv_param_of_le hf hm k (by omega)) e)

section Integral

variable [CompleteSpace G] {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
theorem hasFDerivAt_integral_iteratedFDeriv_param_of_lt {N : ℕ} {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ N (f · x))
    (hm : ∀ k : ℕ, k ≤ N → ∀ e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k : ℕ, k ≤ N → ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) {k : ℕ} (hk : k < N) (e : E) :
    HasFDerivAt (fun e => ∫ x, iteratedFDeriv ℝ k (f · x) e ∂μ)
      (∫ x, fderiv ℝ (fun e => iteratedFDeriv ℝ k (f · x) e) e ∂μ) e := by
  obtain ⟨B, hBi, hB⟩ := hb (k + 1) hk
  obtain ⟨B₀, hB₀i, hB₀⟩ := hb k hk.le
  have hdiff : ∀ x, Differentiable ℝ (fun e => iteratedFDeriv ℝ k (f · x) e) := fun x =>
    (hf x).differentiable_iteratedFDeriv (by exact_mod_cast hk)
  have hm' : AEStronglyMeasurable
      (fun x => fderiv ℝ (fun e => iteratedFDeriv ℝ k (f · x) e) e) μ := by
    have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E)
      G).continuous.comp_aestronglyMeasurable (hm (k + 1) hk e)
    exact this
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ) (bound := B)
    Filter.univ_mem (Eventually.of_forall fun e' => hm k hk.le e')
    (hB₀i.mono' (hm k hk.le e) (by filter_upwards [hB₀] with x hx using hx e)) hm'
    (by filter_upwards [hB] with x hx e' _; rw [norm_fderiv_iteratedFDeriv]; exact hx e')
    hBi (Eventually.of_forall fun x e' _ => (hdiff x e').hasFDerivAt)

omit [FiniteDimensional ℝ E] in
/-- **Differentiation under the integral sign to order `N`.** -/
theorem iteratedFDeriv_integral_param_of_le {N : ℕ} {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ N (f · x))
    (hm : ∀ k : ℕ, k ≤ N → ∀ e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k : ℕ, k ≤ N → ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) :
    ∀ k : ℕ, k ≤ N → iteratedFDeriv ℝ k (fun e => ∫ x, f e x ∂μ) =
      fun e => ∫ x, iteratedFDeriv ℝ k (f · x) e ∂μ
  | 0, _ => by
    funext e
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry.integral_comp_comm
      _).symm
  | k + 1, hk => by
    funext e
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      iteratedFDeriv_integral_param_of_le hf hm hb k (by omega),
      (hasFDerivAt_integral_iteratedFDeriv_param_of_lt hf hm hb (by omega) e).fderiv]
    exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) G)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) G).symm.toLinearIsometry
      _).symm

omit [FiniteDimensional ℝ E] in
/-- The parametric integral of a dominated `C^N` family is `C^N`. -/
theorem contDiff_integral_param_of_le {N : ℕ} {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ N (f · x))
    (hm : ∀ k : ℕ, k ≤ N → ∀ e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k : ℕ, k ≤ N → ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) :
    ContDiff ℝ N (fun e => ∫ x, f e x ∂μ) := by
  have key := (contDiff_iff_continuous_differentiable (𝕜 := ℝ) (f := fun e => ∫ x, f e x ∂μ)
    (n := (N : ℕ∞))).2 ⟨fun k hk => ?_, fun k hk => ?_⟩
  · exact_mod_cast key
  · have hk' : k ≤ N := by exact_mod_cast hk
    rw [iteratedFDeriv_integral_param_of_le hf hm hb k hk']
    obtain ⟨B, hBi, hB⟩ := hb k hk'
    exact continuous_of_dominated (fun e => hm k hk' e) (fun e => by
      filter_upwards [hB] with x hx using hx e) hBi
      (Eventually.of_forall fun x => (hf x).continuous_iteratedFDeriv (by exact_mod_cast hk'))
  · have hk' : k < N := by exact_mod_cast hk
    rw [iteratedFDeriv_integral_param_of_le hf hm hb k hk'.le]
    exact fun e => (hasFDerivAt_integral_iteratedFDeriv_param_of_lt hf hm hb hk' e).differentiableAt

end Integral

/-! ### Coordinate words bound a multilinear map on `ℝ^d` -/

/-- `‖A‖ ≤ ∑_w ‖A(e_{w₁}, …, e_{wₙ})‖` for a multilinear map on Euclidean `ℝ^d`. -/
theorem norm_le_sum_coordWords {d n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) F) :
    ‖A‖ ≤ ∑ w : Fin n → Fin d, ‖A (fun i => EuclideanSpace.single (w i) 1)‖ := by
  classical
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun i => ∑ j, (v i j) • EuclideanSpace.single j (1 : ℝ) := by
    funext i
    ext j
    simp [Pi.single_apply]
  rw [hv, A.map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [A.map_smul_univ, norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  have hi : ∑ j, v i j • EuclideanSpace.single j (1 : ℝ) = v i := by
    ext j
    simp [Pi.single_apply]
  beta_reduce
  rw [hi]
  exact PiLp.norm_apply_le (v i) (w i)

end WaveTurbulence.Regref

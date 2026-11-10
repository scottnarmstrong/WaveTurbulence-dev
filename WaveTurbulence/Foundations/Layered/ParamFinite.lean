/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.ParamDeriv

/-!
# Differentiation under the integral sign to a finite order

The finite-order companion of `ClassJR.ParamDeriv`. For `f(e, x)` that is `C^N` in `e ∈ E` (finite
dimensional) for every `x`, with each iterated `e`-derivative of order `≤ N` measurable in `x` and
dominated uniformly in `e` by an integrable function of `x`:

* `stronglyMeasurable_iteratedFDeriv_param_of_le`: measurability of the iterated derivatives of order
  `≤ N` from measurability of `f(e, ·)` (difference quotients);
* `iteratedFDeriv_integral_param_of_le`: the iterated derivatives of `e ↦ ∫ f(e, x) dμ` of order `≤ N`
  are the integrals of the iterated derivatives;
* `contDiff_integral_param_of_le`: `e ↦ ∫ f(e, x) dμ` is `C^N`.

Used for the momentum derivatives of time-Fourier transforms and their traces (TARGET (normX), L581),
where the transforms are only `C^{Λ₁}` in the momentum.
-/

public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace WaveTurbulence.Layered

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {Z : Type*} [MeasurableSpace Z]

section Integral

variable [CompleteSpace G] {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
/-- One step of differentiation under the integral sign for the `k`-th derivative, `k < N`. -/
theorem hasFDerivAt_integral_iteratedFDeriv_param_of_lt {N : ℕ} {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ N (f · x))
    (hm : ∀ k ≤ N, ∀ e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k ≤ N, ∃ B : X → ℝ, Integrable B μ ∧
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
    (hm : ∀ k ≤ N, ∀ e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k ≤ N, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) :
    ∀ k ≤ N, iteratedFDeriv ℝ k (fun e => ∫ x, f e x ∂μ) =
      fun e => ∫ x, iteratedFDeriv ℝ k (f · x) e ∂μ := by
  intro k
  induction k with
  | zero =>
    intro _
    funext e
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry.integral_comp_comm
      _).symm
  | succ k ih =>
    intro hk
    funext e
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih (by omega),
      (hasFDerivAt_integral_iteratedFDeriv_param_of_lt hf hm hb (by omega) e).fderiv]
    exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) G)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) G).symm.toLinearIsometry
      _).symm

omit [FiniteDimensional ℝ E] in
/-- **The parametric integral of a dominated `C^N` family is `C^N`.** -/
theorem contDiff_integral_param_of_le {N : ℕ} {f : E → X → G}
    (hf : ∀ x, ContDiff ℝ N (f · x))
    (hm : ∀ k ≤ N, ∀ e, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (f · x) e) μ)
    (hb : ∀ k ≤ N, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ e, ‖iteratedFDeriv ℝ k (f · x) e‖ ≤ B x) :
    ContDiff ℝ N (fun e => ∫ x, f e x ∂μ) := by
  rw [show ((N : WithTop ℕ∞)) = ((N : ℕ∞) : WithTop ℕ∞) from rfl,
    contDiff_iff_continuous_differentiable]
  refine ⟨fun m hm' => ?_, fun m hm' => ?_⟩
  · have hmN : m ≤ N := by exact_mod_cast hm'
    rw [iteratedFDeriv_integral_param_of_le hf hm hb m hmN]
    obtain ⟨B, hBi, hB⟩ := hb m hmN
    exact continuous_of_dominated (fun e => hm m hmN e) (fun e => by
      filter_upwards [hB] with x hx using hx e) hBi (Eventually.of_forall fun x =>
        (hf x).continuous_iteratedFDeriv (by exact_mod_cast hmN))
  · have hmN : m < N := by exact_mod_cast hm'
    rw [iteratedFDeriv_integral_param_of_le hf hm hb m hmN.le]
    exact fun e => (hasFDerivAt_integral_iteratedFDeriv_param_of_lt hf hm hb hmN e).differentiableAt

end Integral

end WaveTurbulence.Layered

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Finite smoothness of integrals from actual derivative envelopes

A conditional transport lemma for the spatial assembly of Proposition 5.1.
All derivatives in its hypotheses are actual Fréchet derivatives.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

universe u

/-- Actual higher derivatives of a derivative are obtained by a fixed continuous currying map. -/
theorem iteratedFDeriv_fderiv_eq_curryRight {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fderiv ℝ f) x =
      continuousMultilinearCurryRightEquiv' ℝ j E F (iteratedFDeriv ℝ (j + 1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- Conditional finite-smoothness transport through an integral with actual uniform derivative
bounds. The source applications supply these envelopes from finite spatial input norms. -/
theorem contDiff_integral_of_uniform_derivative_bounds {E F : Type u} {U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace U] (μ : Measure U) (N : ℕ)
    (A : E → U → F) (v : ℕ → U → ℝ)
    (hA : ∀ u, ContDiff ℝ N (fun x => A x u))
    (hmeas : ∀ j ≤ N, ∀ x, AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun y => A y u) x) μ)
    (hv : ∀ j ≤ N, Integrable (v j) μ)
    (hb : ∀ j ≤ N, ∀ x u, ‖iteratedFDeriv ℝ j (fun y => A y u) x‖ ≤ v j u) :
    ContDiff ℝ N (fun x => ∫ u, A x u ∂μ) := by
  induction N generalizing F v with
  | zero =>
      apply contDiff_zero.mpr
      have hm (x : E) : AEStronglyMeasurable (A x) μ := by
        have h := hmeas 0 le_rfl x
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using
          (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable h
      apply continuous_of_dominated hm (fun x => ae_of_all _ (fun u => ?_)) (hv 0 le_rfl)
        (ae_of_all _ (fun u => (hA u).continuous))
      simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl x u
  | succ N ih =>
      let D := fun x u => fderiv ℝ (fun y => A y u) x
      have hD (u : U) : ContDiff ℝ N (fun x => D x u) :=
        (hA u).fderiv_right (by simp)
      have hmD (j : ℕ) (hj : j ≤ N) (x : E) :
          AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun y => D y u) x) μ := by
        have h := hmeas (j + 1) (by omega) x
        have he (u : U) := iteratedFDeriv_fderiv_eq_curryRight (fun y => A y u) j x
        change AEStronglyMeasurable
          (fun u => iteratedFDeriv ℝ j (fderiv ℝ (fun y => A y u)) x) μ
        simp_rw [he]
        exact (continuousMultilinearCurryRightEquiv' ℝ j E F).continuous.comp_aestronglyMeasurable h
      have hbD (j : ℕ) (hj : j ≤ N) (x : E) (u : U) :
          ‖iteratedFDeriv ℝ j (fun y => D y u) x‖ ≤ v (j + 1) u := by
        rw [show (fun y => D y u) = fderiv ℝ (fun y => A y u) from rfl,
          norm_iteratedFDeriv_fderiv]
        exact hb (j + 1) (by omega) x u
      have hCD : ContDiff ℝ N (fun x => ∫ u, D x u ∂μ) :=
        ih D (fun j => v (j + 1)) hD hmD (fun j hj => hv (j + 1) (by omega)) hbD
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨(fun x => ∫ u, D x u ∂μ), hCD, ?_⟩
      intro x
      have hm (y : E) : AEStronglyMeasurable (A y) μ := by
        have h := hmeas 0 (by omega) y
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using
          (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable h
      have hmd (y : E) : AEStronglyMeasurable (D y) μ := by
        have h := hmD 0 (by omega) y
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using
          (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).continuous.comp_aestronglyMeasurable h
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := v 1)
        (Filter.univ_mem) (Filter.Eventually.of_forall hm)
        ((hv 0 (by omega)).mono' (hm x) (ae_of_all _ (fun u => by
          simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) x u))) (hmd x)
        (ae_of_all _ (fun u y _ => ?_)) (hv 1 (by omega))
        (ae_of_all _ (fun u y _ => ((hA u).differentiable (by simp) y).hasFDerivAt))
      simpa only [norm_iteratedFDeriv_zero] using hbD 0 (by omega) y u

end WaveTurbulence.Incoh

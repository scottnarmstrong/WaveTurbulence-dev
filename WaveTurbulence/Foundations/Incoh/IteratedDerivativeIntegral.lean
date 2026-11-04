/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothParameterIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual finite iterated derivatives commute with dominated parameter integrals -/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

universe u

/-- Conditional differentiation transport. All derivative envelopes are actual derivatives;
source applications discharge them using the literal spatial norms. -/
theorem iteratedFDeriv_integral_of_uniform_derivative_bounds {E F : Type u} {U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace U] (μ : Measure U) (N : ℕ)
    (A : E → U → F) (v : ℕ → U → ℝ)
    (hA : ∀ u, ContDiff ℝ N (fun x => A x u))
    (hmeas : ∀ j ≤ N, ∀ x, AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun y => A y u) x) μ)
    (hv : ∀ j ≤ N, Integrable (v j) μ)
    (hb : ∀ j ≤ N, ∀ x u, ‖iteratedFDeriv ℝ j (fun y => A y u) x‖ ≤ v j u)
    (j : ℕ) (hj : j ≤ N) :
    iteratedFDeriv ℝ j (fun x => ∫ u, A x u ∂μ) =
      fun x => ∫ u, iteratedFDeriv ℝ j (fun y => A y u) x ∂μ := by
  induction j with
  | zero =>
      funext x
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.integral_comp_comm (A x)).symm
  | succ j ih =>
      let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedAddCommGroup (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedSpace ℝ (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F) := inferInstance
      let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F) := inferInstance
      have hjN : j ≤ N := by omega
      have he := ih hjN
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, he]
      let D := fun x u => iteratedFDeriv ℝ j (fun y => A y u) x
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F
      have hd (y : E) (u : U) : fderiv ℝ (fun z => D z u) y =
          L (iteratedFDeriv ℝ (j + 1) (fun z => A z u) y) := by
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
      have hmD (y : E) : AEStronglyMeasurable (D y) μ := hmeas j hjN y
      have hmDd (y : E) : AEStronglyMeasurable (fun u => fderiv ℝ (fun z => D z u) y) μ := by
        simp_rw [hd]
        exact L.continuous.comp_aestronglyMeasurable (hmeas (j + 1) hj y)
      have hdiff : HasFDerivAt (fun y => ∫ u, D y u ∂μ)
          (∫ u, fderiv ℝ (fun z => D z u) x ∂μ) x := by
        apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := v (j + 1))
          Filter.univ_mem (Filter.Eventually.of_forall hmD)
          ((hv j hjN).mono' (hmD x) (ae_of_all _ (fun u => hb j hjN x u))) (hmDd x)
          (ae_of_all _ (fun u y _ => ?_)) (hv (j + 1) hj)
          (ae_of_all _ (fun u y _ => ((hA u).differentiable_iteratedFDeriv
            (by exact_mod_cast (show j < N by omega)) y).hasFDerivAt))
        rw [hd, LinearIsometryEquiv.norm_map]
        exact hb (j + 1) hj y u
      rw [hdiff.fderiv]
      change L.symm (∫ u, fderiv ℝ (fun z => D z u) x ∂μ) = _
      calc
        _ = ∫ u, L.symm (fderiv ℝ (fun z => D z u) x) ∂μ :=
          (L.symm.toLinearIsometry.integral_comp_comm (fun u => fderiv ℝ (fun z => D z u) x)).symm
        _ = _ := integral_congr_ae (ae_of_all _ (fun u => by
          dsimp only
          rw [hd, LinearIsometryEquiv.symm_apply_apply]))

end WaveTurbulence.Incoh

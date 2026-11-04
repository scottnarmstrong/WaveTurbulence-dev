/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Norm control of nested actual Fréchet derivatives

The currying maps in the definition of iterated derivatives are linear
isometries. Finite source smoothness therefore controls a derivative of
an iterated derivative without assuming infinite smoothness.
-/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Nested actual derivatives have no operator-norm loss relative to the total derivative. -/
theorem norm_iteratedFDeriv_iteratedFDeriv_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ℕ} {f : E → F} (hf : ContDiff ℝ N f) (j k : ℕ) (hjk : j + k ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ j f) x‖ ≤ ‖iteratedFDeriv ℝ (j + k) f x‖ := by
  induction j generalizing k with
  | zero =>
      let L := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hL : ‖L‖ ≤ 1 := (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.norm_toContinuousLinearMap_le
      change ‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ _
      calc
        _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k f x‖ :=
          L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (show k ≤ N by omega))
        _ ≤ 1 * ‖iteratedFDeriv ℝ k f x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
        _ = _ := by rw [one_mul, Nat.zero_add]
  | succ j ih =>
      let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedAddCommGroup (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedSpace ℝ (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) := inferInstance
      let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F) := inferInstance
      let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F) := inferInstance
      let L : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hL : ‖L‖ ≤ 1 := by
        apply L.opNorm_le_bound zero_le_one
        intro A
        change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm A‖ ≤ 1 * ‖A‖
        rw [LinearIsometryEquiv.norm_map, one_mul]
      have hg : ContDiff ℝ (k + 1) (iteratedFDeriv ℝ j f) :=
        hf.iteratedFDeriv_right (by exact_mod_cast (show (k + 1) + j ≤ N by omega))
      have hgd : ContDiff ℝ k (fderiv ℝ (iteratedFDeriv ℝ j f)) :=
        hg.fderiv_right (by simp)
      change ‖iteratedFDeriv ℝ k (L ∘ fderiv ℝ (iteratedFDeriv ℝ j f)) x‖ ≤ _
      calc
        _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ (iteratedFDeriv ℝ j f)) x‖ :=
          L.norm_iteratedFDeriv_comp_left hgd.contDiffAt (le_refl (k : ℕ∞ω))
        _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ (iteratedFDeriv ℝ j f)) x‖ :=
          mul_le_mul_of_nonneg_right hL (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ (k + 1) (iteratedFDeriv ℝ j f) x‖ := by
          rw [one_mul, norm_iteratedFDeriv_fderiv]
        _ ≤ ‖iteratedFDeriv ℝ (j + (k + 1)) f x‖ := ih (k + 1) (by omega)
        _ = _ := by rw [show j + (k + 1) = j + 1 + k by omega]

end WaveTurbulence.Incoh

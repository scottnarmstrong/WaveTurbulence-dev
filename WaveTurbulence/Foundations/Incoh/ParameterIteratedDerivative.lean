/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth dependence of actual partial iterated derivatives on a parameter -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Joint smoothness gives smooth parameter dependence of all actual partial derivatives. -/
theorem contDiff_parameter_iteratedFDeriv {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → F → G)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × F => iteratedFDeriv ℝ j (f p.1) p.2) := by
  induction j with
  | zero =>
      change ContDiff ℝ ∞ ((continuousMultilinearCurryFin0 ℝ F G).symm ∘ Function.uncurry f)
      exact (continuousMultilinearCurryFin0 ℝ F G).symm.contDiff.comp hf
  | succ j ih =>
      let g := fun p : E × F => iteratedFDeriv ℝ j (f p.1) p.2
      have hg : ContDiff ℝ ∞ (fun p : (E × F) × F => g (p.1.1, p.2)) :=
        ih.comp (by fun_prop)
      have hd : ContDiff ℝ ∞ (fun p : E × F =>
          fderiv ℝ (fun y => g (p.1, y)) p.2) :=
        hg.fderiv (by fun_prop) (by simp)
      have hh := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => F) G).symm.contDiff.comp hd
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      exact hh

end WaveTurbulence.Incoh

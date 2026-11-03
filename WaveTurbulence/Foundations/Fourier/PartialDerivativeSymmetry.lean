/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-!
# Symmetry of the frozen coordinate partial derivatives

The source mixed derivative uses one fixed order. Smoothness identifies
it with the reverse order whenever one-dimensional fundamental-theorem
bounds are applied in the other coordinate direction.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Two frozen coordinate partials are evaluations of the second Fréchet derivative. -/
theorem partialDeriv_partialDeriv_eq_secondFDeriv {r : ℕ} {F : (Fin r → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (i j : Fin r) (x : Fin r → ℝ) :
    WaveTurbulence.partialDeriv i (WaveTurbulence.partialDeriv j F) x =
      fderiv ℝ (fderiv ℝ F) x (Pi.single i 1) (Pi.single j 1) := by
  have hj := WaveTurbulence.contDiff_infty_partialDeriv hF j
  rw [WaveTurbulence.partialDeriv_eq_fderiv_fun (hj.differentiable (by simp)) i,
    WaveTurbulence.partialDeriv_eq_fderiv_fun (hF.differentiable (by simp)) j]
  have hdC : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hd : Differentiable ℝ (fderiv ℝ F) := hdC.differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ F y (Pi.single j 1)) x (Pi.single i 1) = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (c := Pi.single j 1))]
  simp

/-- Smooth frozen coordinate partial derivatives commute. -/
theorem partialDeriv_comm {r : ℕ} {F : (Fin r → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (i j : Fin r) :
    WaveTurbulence.partialDeriv i (WaveTurbulence.partialDeriv j F) =
      WaveTurbulence.partialDeriv j (WaveTurbulence.partialDeriv i F) := by
  funext x
  rw [partialDeriv_partialDeriv_eq_secondFDeriv hF,
    partialDeriv_partialDeriv_eq_secondFDeriv hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end WaveTurbulence.Fourier

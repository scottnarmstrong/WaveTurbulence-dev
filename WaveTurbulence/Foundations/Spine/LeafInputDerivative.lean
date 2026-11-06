/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafProductDerivative
/-! Real coordinate derivatives are the literal real profiles used by the source leafwise kernels. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

noncomputable def realPartialMom {d : ℕ} (j : Fin d) (H : Mom d → ℝ) : Mom d → ℝ :=
  fun x => fderiv ℝ H x (EuclideanSpace.single j 1)

theorem partialMom_ofReal {d : ℕ} (j : Fin d) (H : Mom d → ℝ) (x : Mom d)
    (hH : DifferentiableAt ℝ H x) :
    partialMom j (fun y => (H y : ℂ)) x = (realPartialMom j H x : ℂ) := by
  unfold partialMom realPartialMom
  have he : (fun y => (H y : ℂ)) = Complex.ofRealCLM ∘ H := rfl
  have hcomp : HasFDerivAt (Complex.ofRealCLM ∘ H)
      (Complex.ofRealCLM.comp (fderiv ℝ H x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hH.hasFDerivAt
  rw [he, hcomp.fderiv]
  rfl

theorem realPartialMom_eq_re {d : ℕ} (j : Fin d) (H : Mom d → ℝ)
    (hH : Differentiable ℝ H) :
    realPartialMom j H = fun x => (partialMom j (fun y => (H y : ℂ)) x).re := by
  funext x
  rw [partialMom_ofReal j H x (hH x), Complex.ofReal_re]

theorem contDiff_realPartialMom {d A : ℕ} (j : Fin d) (H : Mom d → ℝ)
    (hH : ContDiff ℝ (A + 1 : ℕ) H) : ContDiff ℝ A (realPartialMom j H) := by
  exact (hH.fderiv_right (m := A) (by simp)).clm_apply contDiff_const

end WaveTurbulence.LGSpine

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.KernelExtension
public import WaveTurbulence.Foundations.Sumint.WeightedCutoffInput

/-!
# Agreement with the weighted actual source integral

The source weight factor is placed in the kernel input. Linearity shows
that this normalization retains exact pointwise agreement.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- Scalar linearity of the explicit rectangular kernel, including nonintegrable inputs. -/
theorem kernelExtension_const_mul {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (c h : ℝ) (a : ℂ) (F : (D.S.TVar → ℝ) → ℂ) (z : Fin 3 → ℝ) :
    kernelExtension D hI c h (fun u => a*F u) z = a*kernelExtension D hI c h F z := by
  unfold kernelExtension
  simp_rw [mul_assoc]
  exact integral_const_mul a _

end WaveTurbulence.Sumint

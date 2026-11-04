/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CutoffKernelAgreement
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

/-- The weighted source integral agrees with the same weighted kernel used at both endpoints. -/
theorem weighted_cutoffPhaseIntegral_eq_kernelExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (c h t t' t'' : ℝ) (ht : |t-c| ≤ h) :
    ((sourceWeightDecay D L γ η *
      ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ) *
      (∫ τ in D.timeDom hI t (t'+t) (t''+t), cutoffPhaseSum D L γ δ η p ν r t τ) =
    (Complex.exp ((Real.pi*(∑ v, D.param v)*t : ℝ)*Complex.I) *
      (Real.exp (t-t'-t'') : ℂ)) *
      kernelExtension D hI c h (weightedCutoffInput D L γ δ η p ν r) ![t,t',t''] := by
  rw [cutoffPhaseIntegral_eq_kernelExtension D hI L γ δ η p ν r c h t t' t'' ht]
  unfold weightedCutoffInput
  rw [kernelExtension_const_mul]
  ring

end WaveTurbulence.Sumint

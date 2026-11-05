/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.MomentumSingularScale
public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-! # Literal B2 resonant factors in source link coordinates

These identities are shared by the couple Mstar and chain Nstar recursions.
The source y coordinate is parent-child2, so the third momentum is k-y.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Resonant

variable {d : ℕ}

/-- The B2 delta factor is exactly the landed momentum-conserving integral. -/
theorem b2_resIntegral_eq (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    resIntegral Ψ k = deltaInt (resonantKernel Ψ k) := rfl

/-- The B2 symmetric quotient is exactly the landed real PV formula. -/
theorem b2_pvResonantIntegral_eq (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    pvResonantIntegral Ψ k = ∫ ℓ, energyInvSliceLimit (resonantKernel Ψ k) ℓ := rfl

/-- Actual source-link delta integration contributes twice the B2 factor. -/
theorem deltaInner_source_momentum (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    NTSP.deltaInner (fun x y => (Ψ (k+x) (k+x-y) (k-y):ℂ)) =
      (2:ℂ)*(resIntegral Ψ k:ℂ) := by
  simpa only [b2_resIntegral_eq,resonantKernel,sub_eq_add_neg] using
    deltaInner_neg_right_ofReal (resonantKernel Ψ k)

/-- Actual source-link principal value contributes twice the literal B2
factor; its convergence is proved from the kernel and gradient decay. -/
theorem pvOp_source_momentum_of_decay
    (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d)
    {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ} (hd : 0 < d)
    (hF : DeltaKernel (resonantKernel Ψ k) A a N)
    (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ))
    (hD : ∀ ℓ x, HasFDerivAt (resonantKernel Ψ k ℓ) (D ℓ x) x) :
    pvOp (fun x y => (Ψ (k+x) (k+x-y) (k-y):ℂ)) =
      (2:ℂ)*(pvResonantIntegral Ψ k:ℂ) := by
  simpa only [resonantKernel,sub_eq_add_neg, b2_pvResonantIntegral_eq] using
    pvOp_neg_right_ofReal_of_decay hd hF hgrad hDc hD

end WaveTurbulence.RegAsymp

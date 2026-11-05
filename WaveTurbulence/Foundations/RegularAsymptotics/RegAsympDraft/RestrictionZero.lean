/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # The literal full mixed restriction norm of zero -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier

/-- Zero satisfies the landed integrability/smoothness guard and has zero
full mixed Fourier norm at every finite spatial order. -/
theorem mixedFourierNorm_zero {r d : ℕ} (θ : ℝ) (N W : ℕ) :
    mixedFourierNorm θ N W (fun (_ : Fin r → ℝ) (_ : Mom d) => 0) = 0 := by
  have hTF : mixedTimeFourier (fun (_ : Fin r → ℝ) (_ : Mom d) => (0:ℂ)) = fun _ _ => 0 := by
    funext ξ k
    exact congrFun (timeFourier_zero r) ξ
  have hg : MixedFourierAdmissible N (fun (_ : Fin r → ℝ) (_ : Mom d) => (0:ℂ)) := by
    refine ⟨fun _ => integrable_zero _ _ _,Or.inr ?_⟩
    rw [hTF]
    exact ae_of_all _ (fun _ => contDiff_const)
  simp only [mixedFourierNorm,hg,ite_true,hTF]
  simp [momentumSupNorm,momentumDerivative]

/-- The zero extension gives zero full restriction norm on arbitrary sets. -/
theorem mixedRestrictionNorm_zero {r d : ℕ} (θ : ℝ) (N W : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) :
    mixedRestrictionNorm θ N W T K (fun _ _ => 0) = 0 := by
  apply le_antisymm _ zero_le
  exact (mixedRestrictionNorm_le_extension (fun _ _ => 0) (fun _ _ => rfl)).trans_eq
    (mixedFourierNorm_zero θ N W)

end WaveTurbulence.RegAsymp

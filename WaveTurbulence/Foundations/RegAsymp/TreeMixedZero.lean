/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Fourier.TimeBasic

/-! # The exact guarded mixed norm of the zero extension -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory

/-- The actual guarded full mixed norm of the zero function is zero at every order. -/
theorem tree_mixedFourierNorm_zero {r d : ℕ} (θ : ℝ) (N W : ℕ) :
    Fourier.mixedFourierNorm (r := r) (d := d) θ N W (fun _ _ => (0:ℂ))=0 := by
  classical
  have hFT : Fourier.mixedTimeFourier (r := r) (d := d) (fun _ _ => (0:ℂ))=fun _ _ => 0 := by
    funext ξ k
    exact congrFun (Fourier.timeFourier_zero r) ξ
  have hadm : Fourier.MixedFourierAdmissible (r := r) (d := d) N (fun _ _ => (0:ℂ)) := by
    refine ⟨fun _ => integrable_zero _ _ _,Or.inr ?_⟩
    rw [hFT]
    exact ae_of_all _ (fun _ => contDiff_const)
  have hder {n : ℕ} (ρ : Fin n → Fin d) :
      Fourier.momentumDerivative ρ (fun _ : Mom d => (0:ℂ))=fun _ => 0 := by
    funext k
    by_cases hn : n=0
    · subst n
      simp only [Fourier.momentumDerivative_zero]
    · rw [Fourier.momentumDerivative,iteratedFDeriv_const_of_ne hn]
      rfl
  rw [Fourier.mixedFourierNorm,ite_eq_left hadm]
  simp [hFT,hder,Fourier.momentumSupNorm]

end WaveTurbulence.RegAsymp

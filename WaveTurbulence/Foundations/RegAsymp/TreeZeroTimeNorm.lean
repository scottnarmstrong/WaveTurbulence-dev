/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V

/-! # The mixed Fourier norm without time coordinates is the spatial norm -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory

/-- The zero-dimensional time Fourier transform is evaluation at the unique point. -/
theorem tree_timeFourier_zero_time (f : (Fin 0 → ℝ) → ℂ) (ξ : Fin 0 → ℝ) :
    Fourier.timeFourier f ξ = f Fin.elim0 := by
  simp [Fourier.timeFourier, VectorFourier.fourierIntegral,
    Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ)),
    Fourier.timePairing, dotProduct]

/-- Every zero-dimensional frequency has weight one. -/
theorem tree_timeWeight_zero_time (θ : ℝ) (ξ : Fin 0 → ℝ) : Fourier.timeWeight θ ξ = 1 := by
  have hnone : (default : Option (Fin 0)) = none := by
    cases h : (default : Option (Fin 0)) with
    | none => rfl
    | some i => exact Fin.elim0 i
  simp [Fourier.timeWeight, Fourier.timeBracket, hnone]

/-- There is no extra frequency or admissibility cost when the time space is a point. -/
theorem tree_mixedFourierNorm_zero_time {d : ℕ} (θ : ℝ) (N W : ℕ)
    (f : Mom d → ℂ) :
    Fourier.mixedFourierNorm (r := 0) θ N W (fun _ => f) = Fourier.spatialNorm N W f := by
  classical
  have htime : Fourier.mixedTimeFourier (r := 0) (fun _ => f) = fun _ => f := by
    funext ξ k
    exact tree_timeFourier_zero_time _ ξ
  have hi (k : Mom d) : Integrable (fun _ : Fin 0 → ℝ => f k) := by
    rw [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ))]
    exact integrable_const _
  have ha : Fourier.MixedFourierAdmissible N (r := 0) (fun _ => f) ↔
      N = 0 ∨ ContDiff ℝ N f := by
    simp only [Fourier.MixedFourierAdmissible, hi, htime]
    rw [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ))]
    simp
  simp only [Fourier.mixedFourierNorm, Fourier.spatialNorm, ha, htime, tree_timeWeight_zero_time, one_mul]
  simp only [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ)), lintegral_dirac]

/-- Without time variables the vector-family norm is the pointwise supremum. -/
theorem tree_mixedFourierNorm00_zero_time {U : Type*} (θ : ℝ) (f : U → ℂ) :
    Fourier.mixedFourierNorm00 (r := 0) θ (fun _ => f) = ⨆ u, ‖f u‖ₑ := by
  have hi (u : U) : Integrable (fun _ : Fin 0 → ℝ => f u) := by
    rw [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ))]
    exact integrable_const _
  rw [Fourier.mixedFourierNorm00_eq_lintegral hi]
  simp only [Fourier.mixedFourierEnvelope00, tree_timeFourier_zero_time,
    tree_timeWeight_zero_time, one_mul,
    Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ)), lintegral_dirac]

end WaveTurbulence.RegAsymp

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedBoxBound
public import WaveTurbulence.Foundations.Fourier.TwoCoordinateIntegration
import Mathlib.Tactic

/-!
# Nonnegative box integral algebra

Monotonicity and extraction of finite constants reduce ordered-amplitude
bounds to ordinary local `L¹` estimates in two distinguished coordinates.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Monotonicity of the recursively defined box integral. -/
theorem boxIntegral_mono (n : ℕ) {f g : (Fin n → ℝ) → ℝ≥0∞}
    (h : ∀ v, f v ≤ g v) (R : ℝ) : boxIntegral n f R ≤ boxIntegral n g R := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    apply lintegral_mono
    intro u
    exact ih (fun v => h (Fin.cons u v))

/-- A finite nonnegative scalar factors out of a box integral. -/
theorem boxIntegral_const_mul (n : ℕ) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (f : (Fin n → ℝ) → ℝ≥0∞) (R : ℝ) :
    boxIntegral n (fun v => c * f v) R = c * boxIntegral n f R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [boxIntegral, ih]
    exact lintegral_const_mul' _ _ hc

/-- The integral of a constant is box volume times that constant. -/
theorem boxIntegral_const (n : ℕ) (c : ℝ≥0∞) (R : ℝ) :
    boxIntegral n (fun _ => c) R = volume (Icc (-R) R) ^ n * c := by
  induction n with
  | zero => simp [boxIntegral]
  | succ n ih =>
    simp [boxIntegral, ih, pow_succ, mul_comm, mul_left_comm]

/-- Two-coordinate box integration in the paper's vector notation. -/
theorem boxIntegral_two (f : (Fin 2 → ℝ) → ℝ≥0∞) (R : ℝ) :
    boxIntegral 2 f R = ∫⁻ u in Icc (-R) R, ∫⁻ v in Icc (-R) R, f ![u, v] := by
  simp only [boxIntegral]
  congr 1

/-- A two-coordinate box integral is bounded by the full Lebesgue integral. -/
theorem boxIntegral_two_le_lintegral {f : (Fin 2 → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) : boxIntegral 2 f R ≤ ∫⁻ x, f x := by
  rw [boxIntegral_two, lintegral_two_coordinates hf]
  calc
    _ ≤ ∫⁻ u in Icc (-R) R, ∫⁻ v : ℝ, f ![u, v] :=
      lintegral_mono (fun _ => setLIntegral_le_lintegral _ _)
    _ ≤ _ := setLIntegral_le_lintegral _ _

end WaveTurbulence.Fourier

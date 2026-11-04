/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceExitTransform
public import WaveTurbulence.Foundations.Sumint.SourceEndpointSelectedSupport

/-!
# Sparse endpoint transforms are exact selected-coordinate Fourier transforms

Distinct endpoint and distinguished times use two native coordinates.
When they coincide, their frequencies combine into one coordinate.
The coefficient is exactly the actual zero-extended endpoint input.
-/

public section
open MeasureTheory Set
open scoped Classical
namespace WaveTurbulence.Sumint

/-- Two distinct native input times form an injective selected-coordinate list. -/
theorem sourceExitSelectedTwo_injective {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (v : D.S.TVar) (hv : v ≠ firstTime D hI) : Function.Injective (![v,firstTime D hI] : Fin 2 → D.S.TVar) := by
  intro j k h
  fin_cases j <;> fin_cases k
  all_goals first | rfl | exact False.elim (hv h) | exact False.elim (hv h.symm)

/-- The two-coordinate Fourier character is exactly the native sparse endpoint phase. -/
theorem selectedCoordinateCharacter_exit_two {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (v : D.S.TVar) (α ζ : ℝ) (u : D.S.TVar → ℝ) :
    selectedCoordinateCharacter (![v,firstTime D hI] : Fin 2 → D.S.TVar) ![-α,ζ] u =
      sourceExitPhase D hI v α ζ u := by
  unfold selectedCoordinateCharacter sourceExitPhase
  apply congrArg (fun x : ℝ => (Real.fourierChar x:ℂ))
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- The coincident endpoint character is the original one-coordinate Fourier character. -/
theorem selectedCoordinateCharacter_exit_one {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (α ζ : ℝ) (u : D.S.TVar → ℝ) :
    selectedCoordinateCharacter (fun _ : Fin 1 => firstTime D hI) (fun _ => ζ-α) u =
      sourceExitPhase D hI (firstTime D hI) α ζ u := by
  unfold selectedCoordinateCharacter sourceExitPhase
  apply congrArg (fun x : ℝ => (Real.fourierChar x:ℂ))
  simp only [Fin.sum_univ_one]
  ring

/-- The actual sparse endpoint transform is the full native integral of its exact zero extension. -/
theorem sourceExitTransform_eq_zeroExtension_integral {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) (α ζ : ℝ) :
    sourceExitTransform D hI upper v (weightedCutoffInput D L γ δ η p ν r) c h α ζ =
      ∫ u, sourceExitPhase D hI v α ζ u*sourceExitInput D hI L γ δ η p ν r c h upper v u := by
  unfold sourceExitTransform
  rw [← integral_indicator (measurableSet_localInputTimeDomain D c h)]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  by_cases hu : u ∈ localInputTimeDomain D c h
  · simp only [sourceExitInput,Set.indicator_of_mem hu]
    exact mul_comm _ _
  · simp only [sourceExitInput,Set.indicator_of_notMem hu,mul_zero]

/-- The actual two-time endpoint transform is precisely the Fourier transform of its actual selected marginal. -/
theorem sourceExitTransform_eq_selectedFourier_two {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (v : D.S.TVar) (hv : v ≠ firstTime D hI) (α ζ : ℝ) :
    sourceExitTransform D hI upper v (weightedCutoffInput D L γ δ η p ν r) c h α ζ =
      Fourier.timeFourier (selectedCoordinateMarginal ![v,firstTime D hI]
        (sourceExitSelectedTwo_injective D hI v hv) (sourceExitInput D hI L γ δ η p ν r c h upper v)) ![-α,ζ] := by
  rw [sourceExitTransform_eq_zeroExtension_integral]
  rw [← selectedCoordinate_integral_eq_timeFourier _ _ _
    (integrable_sourceExitInput D hI hL γ δ η hη p ν r c h upper v)]
  simp_rw [selectedCoordinateCharacter_exit_two]

/-- The actual coincident-time endpoint transform is precisely its one-coordinate marginal Fourier transform. -/
theorem sourceExitTransform_eq_selectedFourier_one {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (c h : ℝ) (upper : Bool) (α ζ : ℝ) :
    sourceExitTransform D hI upper (firstTime D hI) (weightedCutoffInput D L γ δ η p ν r) c h α ζ =
      Fourier.timeFourier (selectedCoordinateMarginal (fun _ : Fin 1 => firstTime D hI)
        (fun _ _ _ => Subsingleton.elim _ _) (sourceExitInput D hI L γ δ η p ν r c h upper (firstTime D hI)))
          (fun _ => ζ-α) := by
  rw [sourceExitTransform_eq_zeroExtension_integral]
  have he := selectedCoordinate_integral_eq_timeFourier (fun _ : Fin 1 => firstTime D hI)
    (fun _ _ _ => Subsingleton.elim _ _) (sourceExitInput D hI L γ δ η p ν r c h upper (firstTime D hI))
    (integrable_sourceExitInput D hI hL γ δ η hη p ν r c h upper (firstTime D hI)) (fun _ => ζ-α)
  simpa only [selectedCoordinateCharacter_exit_one] using he

end WaveTurbulence.Sumint

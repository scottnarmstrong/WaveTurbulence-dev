/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedIntegral
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini in head/tail clock coordinates

The finite coordinate split preserves Lebesgue measure exactly.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- A head/tail clock split preserves integrability. -/
theorem integrable_finCons_iff {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ} :
    Integrable (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) ↔ Integrable F := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurableEmbedding (g := F)
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Equiv.coe_fn_mk, Function.comp_def] using h

/-- Integrate first over the tail clocks and then over the root clock. -/
theorem integral_eq_integral_finCons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ} (hF : Integrable F) :
    (∫ v, F v) = ∫ x : ℝ, ∫ v : Fin n → ℝ, F (Fin.cons x v) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Equiv.coe_fn_mk] at h
  change (∫ z : ℝ × (Fin n → ℝ), F (Fin.cons z.1 z.2)) = ∫ v, F v at h
  rw [← h]
  exact integral_prod _ (integrable_finCons_iff.mpr hF)

end WaveTurbulence.Incoh

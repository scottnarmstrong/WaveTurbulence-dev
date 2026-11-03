/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Data.Fin.VecNotation

/-!
# Iterated integrals in three physical coordinates

The elementary Fubini conversion used to integrate the `x` variable first
in TARGET `lemcubic0`.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory

/-- Extract the last coordinate with the standard product Lebesgue measure. -/
theorem integral_fin_snoc {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Integrable f) :
    (∫ p, f p) = ∫ z : ℝ, ∫ q : Fin n → ℝ, f (Fin.snoc q z) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hp : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm _
  have hi : Integrable (fun p => f (e p)) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  rw [← hp.integral_comp' f, Measure.volume_eq_prod, integral_prod _ hi]
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last']

/-- Almost every last-coordinate slice is integrable. -/
theorem integrable_fin_snoc_ae {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Integrable f) :
    ∀ᵐ z : ℝ, Integrable (fun q : Fin n → ℝ => f (Fin.snoc q z)) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hp : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm _
  have hi : Integrable (fun p => f (e p)) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last'] using
    hi.prod_right_ae

/-- A single physical coordinate carries ordinary Lebesgue measure. -/
theorem integral_fin_one (f : (Fin 1 → ℝ) → ℂ) :
    (∫ q, f q) = ∫ x : ℝ, f (fun _ => x) := by
  have hp := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ))
  calc
    _ = ∫ x : ℝ, f ((MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).symm x) :=
      (hp.integral_comp' f).symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      congr 1

/-- Fubini in exactly the coordinate order written as `dx dy dz` in the source. -/
theorem integral_fin_three {f : (Fin 3 → ℝ) → ℂ} (hf : Integrable f) :
    (∫ p, f p) = ∫ z : ℝ, ∫ y : ℝ, ∫ x : ℝ, f ![x, y, z] := by
  rw [integral_fin_snoc hf]
  apply integral_congr_ae
  filter_upwards [integrable_fin_snoc_ae hf] with z hz
  rw [integral_fin_snoc hz]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  rw [integral_fin_one]
  congr 1
  funext x
  congr 1
  ext i
  fin_cases i <;> rfl

end WaveTurbulence.LemLin

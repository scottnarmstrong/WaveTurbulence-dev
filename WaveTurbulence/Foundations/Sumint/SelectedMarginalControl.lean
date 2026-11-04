/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SelectedCoordinateFourier
public import WaveTurbulence.Foundations.Sumint.FiniteSupportL2

/-!
# From native remaining-coordinate mass bounds to selected Fourier L² bounds

This generic conditional helper accepts an explicit remaining-coordinate
mass bound. It does not assert that bound for a source coefficient.
Support in the selected box and its volume bound then give the factor
three, and the proved Fourier L² endpoint transfers it to frequency.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- A native coefficient vanishing outside a selected box has marginal supported in that box. -/
theorem selectedMarginal_eq_zero_of_outside {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ)
    (lo hi : Fin r → ℝ)
    (hfzero : ∀ u, (∃ j, u (v j) ∉ Icc (lo j) (hi j)) → f u = 0)
    (x : Fin r → ℝ) (hx : x ∉ Icc lo hi) : selectedCoordinateMarginal v hv f x = 0 := by
  have hx' : ∃ j, x j ∉ Icc (lo j) (hi j) := by
    by_contra! hh
    exact hx ⟨fun j => (hh j).1,fun j => (hh j).2⟩
  obtain ⟨j,hj⟩ := hx'
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro y
  apply hfzero
  refine ⟨j,?_⟩
  rwa [selectedCoordinateSplit_symm_selected]

/-- A remaining-coordinate nonnegative mass bound controls the norm of the native marginal. -/
theorem norm_selectedMarginal_le_of_mass {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (htrace : ∀ x : Fin r → ℝ,
      (∫⁻ y : {i : ι // i ∉ Set.range v} → ℝ, ‖f ((selectedCoordinateSplit v hv).symm (x,y))‖ₑ) ≤ ENNReal.ofReal B)
    (x : Fin r → ℝ) : ‖selectedCoordinateMarginal v hv f x‖ ≤ B := by
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [ofReal_norm]
  exact (enorm_integral_le_lintegral_enorm _).trans (htrace x)

/-- Explicit remaining-coordinate mass and support bounds give the selected Fourier L² estimate. -/
theorem selectedMarginal_fourier_L2_le_of_mass {ι : Type*} [Fintype ι] {r : ℕ}
    (v : Fin r → ι) (hv : Function.Injective v) (f : (ι → ℝ) → ℂ) (hfm : Measurable f) (hfi : Integrable f)
    (lo hi : Fin r → ℝ) (hvol : volume (Icc lo hi) ≤ ENNReal.ofReal 9)
    {B : ℝ} (hB : 0 ≤ B)
    (htrace : ∀ x : Fin r → ℝ,
      (∫⁻ y : {i : ι // i ∉ Set.range v} → ℝ, ‖f ((selectedCoordinateSplit v hv).symm (x,y))‖ₑ) ≤ ENNReal.ofReal B)
    (hfzero : ∀ u, (∃ j, u (v j) ∉ Icc (lo j) (hi j)) → f u = 0) :
    eLpNorm (Fourier.timeFourier (selectedCoordinateMarginal v hv f)) 2 ≤ ENNReal.ofReal (3*B) := by
  have hm : AEStronglyMeasurable (selectedCoordinateMarginal v hv f) volume :=
    (measurable_selectedCoordinateMarginal v hv f hfm).aestronglyMeasurable
  have hb := norm_selectedMarginal_le_of_mass v hv f hB htrace
  have hz := selectedMarginal_eq_zero_of_outside v hv f lo hi hfzero
  have h2 := memLp_two_of_support_volume_le_nine hm measurableSet_Icc hvol hB (fun x _ => hb x) hz
  exact (eLpNorm_timeFourier_selectedMarginal_le v hv f hfi h2).trans
    (eLpNorm_two_le_three_mul_of_support hm measurableSet_Icc hvol hB (fun x _ => hb x) hz)

end WaveTurbulence.Sumint

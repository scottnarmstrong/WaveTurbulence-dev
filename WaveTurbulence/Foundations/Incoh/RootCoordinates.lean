/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.PoissonBlocks
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Structural root coordinates and root densities

TARGET (incohproof17). A finite coordinate permutation selects the two
root times and the remaining internal times. The carrier stores no norm
estimates. Measure preservation and the marginal L¹ bound are proved.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- A structural split into two root coordinates and the remaining internal times. -/
structure RootCoordinates (n : ℕ) where
  restCount : ℕ
  permutation : Fin (n * 2) ≃ (Fin 2 ⊕ Fin restCount)

/-- The structural coordinate permutation, bundled as a measurable equivalence. -/
@[expose] def RootCoordinates.equiv {n : ℕ} (R : RootCoordinates n) :
    (Fin n → Fin 2 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × (Fin R.restCount → ℝ)) :=
  (Fourier.flattenBlocks n 2).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Fin R.restCount => ℝ) R.permutation).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin R.restCount => ℝ)))

/-- No Jacobian is assumed: finite coordinate permutations preserve product Lebesgue measure. -/
theorem RootCoordinates.measurePreserving {n : ℕ} (R : RootCoordinates n) :
    MeasurePreserving R.equiv :=
  (Fourier.flattenBlocks_measurePreserving n 2).trans
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 2 ⊕ Fin R.restCount => ℝ) R.permutation).trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin R.restCount => ℝ)))

/-- The actual marginal obtained by integrating every non-root time. -/
@[expose] def RootCoordinates.density {n : ℕ} (R : RootCoordinates n)
    (F : (Fin n → Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  ∫ u : Fin R.restCount → ℝ, F (R.equiv.symm (t, u))

/-- Integrability of the full integrand gives integrability of the actual root marginal. -/
theorem RootCoordinates.integrable_density {n : ℕ} (R : RootCoordinates n)
    {F : (Fin n → Fin 2 → ℝ) → ℂ} (hF : Integrable F) : Integrable (R.density F) := by
  have hG : Integrable (fun z => F (R.equiv.symm z)) :=
    (R.measurePreserving.symm.integrable_comp_emb R.equiv.symm.measurableEmbedding).mpr hF
  exact hG.integral_prod_left

/-- TARGET (incohproof18), the L¹ marginal inequality before inserting the product estimate. -/
theorem RootCoordinates.lintegral_density_le {n : ℕ} (R : RootCoordinates n)
    {F : (Fin n → Fin 2 → ℝ) → ℂ} (hF : Integrable F) :
    (∫⁻ t, ‖R.density F t‖ₑ) ≤ ∫⁻ u, ‖F u‖ₑ := by
  have hG : Integrable (fun z => F (R.equiv.symm z)) :=
    (R.measurePreserving.symm.integrable_comp_emb R.equiv.symm.measurableEmbedding).mpr hF
  calc
    _ ≤ ∫⁻ t : Fin 2 → ℝ, ∫⁻ u : Fin R.restCount → ℝ, ‖F (R.equiv.symm (t, u))‖ₑ :=
      lintegral_mono fun _ => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, ‖F (R.equiv.symm z)‖ₑ := (lintegral_prod _ hG.aestronglyMeasurable.enorm).symm
    _ = _ := R.measurePreserving.symm.lintegral_comp_emb R.equiv.symm.measurableEmbedding
      (fun u : Fin n → Fin 2 → ℝ => ‖F u‖ₑ)

end WaveTurbulence.Incoh

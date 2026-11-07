/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.ProductFubini
import Mathlib.Tactic

/-!
# S2 REPRESENTS: exchange of `∑_κ ∫_τ ∑_ξ` with `∑_ξ ∑_κ ∫_τ`
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open MeasureTheory
open scoped ENNReal

/-- `∑_κ ∫_τ ∑_ξ g = ∑_ξ ∑_κ ∫_τ g`, with all three exchanges justified by the finiteness of the total
absolute mass `∑_ξ ∑_κ ∫⁻ ‖g‖`.  Also returns the absolute summability of the double family. -/
theorem sum_integral_sum_swap {Ξ K T : Type*} [Countable Ξ] [Countable K] [MeasurableSpace T]
    (μ : Measure T) (g : Ξ → K → T → ℂ) (hmeas : ∀ ξ κ, AEStronglyMeasurable (g ξ κ) μ)
    (hbound : ∑' ξ, ∑' κ, ∫⁻ τ, ‖g ξ κ τ‖ₑ ∂μ ≠ ⊤) :
    (∑' κ, ∫ τ, ∑' ξ, g ξ κ τ ∂μ = ∑' ξ, ∑' κ, ∫ τ, g ξ κ τ ∂μ) ∧
      Summable (fun p : Ξ × K => ‖∫ τ, g p.1 p.2 τ ∂μ‖) := by
  have hpair : ∑' p : Ξ × K, ∫⁻ τ, ‖g p.1 p.2 τ‖ₑ ∂μ ≠ ⊤ := by
    rw [ENNReal.tsum_prod (f := fun ξ κ => ∫⁻ τ, ‖g ξ κ τ‖ₑ ∂μ)]; exact hbound
  have hK : ∀ κ, ∑' ξ, ∫⁻ τ, ‖g ξ κ τ‖ₑ ∂μ ≠ ⊤ := by
    intro κ
    have h2 : ∑' κ, ∑' ξ, ∫⁻ τ, ‖g ξ κ τ‖ₑ ∂μ ≠ ⊤ := by
      rw [ENNReal.tsum_comm]; exact hbound
    exact ne_top_of_le_ne_top h2 (ENNReal.le_tsum (f := fun κ => ∑' ξ, ∫⁻ τ, ‖g ξ κ τ‖ₑ ∂μ) κ)
  have hnorm : Summable (fun p : Ξ × K => ‖∫ τ, g p.1 p.2 τ ∂μ‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (ENNReal.summable_toReal hpair)
    rw [← integral_norm_eq_lintegral_enorm (hmeas p.1 p.2)]
    exact norm_integral_le_integral_norm _
  refine ⟨?_, hnorm⟩
  have e1 : ∀ κ, ∫ τ, ∑' ξ, g ξ κ τ ∂μ = ∑' ξ, ∫ τ, g ξ κ τ ∂μ := fun κ =>
    integral_tsum (fun ξ => hmeas ξ κ) (hK κ)
  simp_rw [e1]
  have hsum : Summable (fun p : Ξ × K => ∫ τ, g p.1 p.2 τ ∂μ) := hnorm.of_norm
  exact (Summable.tsum_comm' (f := fun (ξ : Ξ) (κ : K) => ∫ τ, g ξ κ τ ∂μ) hsum
    (fun ξ => hsum.prod_factor ξ)
    (fun κ => (hsum.comp_injective Prod.swap_injective).prod_factor κ))

end WaveTurbulence.Represents

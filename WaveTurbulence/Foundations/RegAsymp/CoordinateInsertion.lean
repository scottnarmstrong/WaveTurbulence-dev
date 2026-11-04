/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.Symbol
import Mathlib.Tactic

/-! # One-coordinate insertion in the source ℓ¹ derivative spaces

Inserting a zero coordinate is an isometry. Restricting a coefficient
therefore incurs no dimension-to-the-derivative-order factor.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open WithLp ClassJR
open scoped ContDiff

/-- The actual ℓ¹ insertion of the coordinate frozen by the Wick correction. -/
def optionZeroL1 {ι : Type} [Fintype ι] : L1 ι →ₗᵢ[ℝ] L1 (Option ι) where
  toFun α := toLp 1 (fun o => match o with | none => (0:ℝ) | some i => α i)
  map_add' α β := by
    ext i
    cases i <;> simp
  map_smul' r α := by
    ext i
    cases i <;> simp
  norm_map' α := by
    rw [PiLp.norm_eq_of_L1,PiLp.norm_eq_of_L1]
    simp

/-- Restricting an ℓ¹ derivative tensor to the remaining variables is contractive. -/
theorem norm_iteratedFDeriv_optionZero_le {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : L1 (Option ι) → E}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (β : L1 ι) :
    ‖iteratedFDeriv ℝ k (f ∘ optionZeroL1) β‖ ≤ ‖iteratedFDeriv ℝ k f (optionZeroL1 β)‖ := by
  change ‖iteratedFDeriv ℝ k (f ∘ optionZeroL1.toContinuousLinearMap) β‖ ≤ _
  rw [(optionZeroL1.toContinuousLinearMap).iteratedFDeriv_comp_right hf β (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hi : ‖(optionZeroL1 (ι := ι)).toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (optionZeroL1 β)‖ * ∏ _i : Fin k, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hi)) (norm_nonneg _)
    _ = _ := by simp

end WaveTurbulence.RegAsymp

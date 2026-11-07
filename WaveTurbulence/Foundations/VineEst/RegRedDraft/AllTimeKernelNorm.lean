/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.AllTimeKernel

/-! # Absolute lattice/time bounds on actual full-coordinate kernel summands -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open MeasureTheory

theorem integral_norm_kernelAllIntegrand_eq {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelAllIntegrand L γ δ F LG up s k₀ κ τ‖) =
      (∫ τ, ‖kernelIntegrand L γ δ F LG up s k₀ κ τ‖) := by
  apply ((measurePreserving_allTimeEquiv LG.garden hG).integral_comp'
    (fun τ => ‖kernelAllIntegrand L γ δ F LG up s k₀ κ τ‖)).symm.trans
  exact integral_congr_ae (Filter.Eventually.of_forall (fun τ => congrArg norm
    (kernelAllIntegrand_allTimeEquiv L γ δ F LG hG up s k₀ κ τ)))

theorem integral_norm_kernelAllIntegrand_le {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelAllIntegrand L γ δ F LG up s k₀ κ τ‖) ≤ LGSpine.inputLeafMajorant L F LG k₀ κ :=
  (integral_norm_kernelAllIntegrand_eq L γ δ F LG hG up s k₀ κ).trans_le
    (integral_norm_kernelIntegrand_le L γ δ F LG up s k₀ κ)

/-- The only analytic premise is the source lattice absolute summability of
input functions. Every time-integrability and summed L1 bound is derived. -/
theorem summable_integral_norm_kernelAllIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀+latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, ‖kernelAllIntegrand L γ δ F LG up s k₀ κ τ‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_kernelAllIntegrand_le L γ δ F LG hG up s k₀)
    (LGSpine.summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF)

end WaveTurbulence.RegRed

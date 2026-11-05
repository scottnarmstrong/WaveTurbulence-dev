/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantTreeLeafGroups
/-! The top-tree coefficients have a uniform deterministic time-box bound. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

theorem norm_topTreeCoefficient_le {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (t : Fin w → ℝ) (j : Fin w) :
    ‖topTreeCoefficient L γ δ p top sig n κ t j‖ ≤ boxVol (top j) p (t j) := by
  unfold topTreeCoefficient
  rw [norm_zpowSign, norm_mul]
  exact (mul_le_mul (norm_epsProd_le _ _) (norm_timeInt_le L γ δ _ _ p (t j))
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem norm_prod_topTreeCoefficient_le {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (t : Fin w → ℝ) :
    ‖∏ j, topTreeCoefficient L γ δ p top sig n κ t j‖ ≤ ∏ j, boxVol (top j) p (t j) := by
  rw [norm_prod]
  exact prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun j _ => norm_topTreeCoefficient_le L γ δ p top sig n κ t j)

end WaveTurbulence.Induct

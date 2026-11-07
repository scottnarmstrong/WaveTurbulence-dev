/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFineStrongNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Conditional assembly of the fine normalization factors -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Conditional assembly helper, not a source operation theorem. Source
exports must separately prove the raw count and circuit-rank identity. -/
theorem appb_link_fine_strong_of_countE_and_rank {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) {d : ℕ} (L γ δ C1 η : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (q : Fin P.edges.length → (Fin d → ℤ))
    (scales : Finset V → ℝ) (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 1 ≤ C1) (hη : 0 ≤ η)
    (hlow : ∀ a ∈ r.removedAtoms,M.deg a ≤ 2)
    (hchi : M.circuitRank = r.post.circuitRank+1)
    (hraw : (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
      ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞)) :
    IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
      (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
      (ENNReal.ofReal (L^(-3*η/4))) := by
  have hprod := appbLinkProduct_eraseAtoms_low_degree M r.removedAtoms hlow L γ δ scales
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ.1 _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 :=
    (mul_le_mul ((inv_le_one₀ hCpos).mpr hC1)
      (Real.rpow_le_one hδ.1.le hδ.2 (by norm_num))
      (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have ha := appb_fine_normalization_strong_of_raw _ _ r.post.circuitRank L ((d : ℝ)-γ)
    (C1⁻¹*δ^(1/2 : ℝ)) (appbLinkProduct r.post L γ δ scales) η hL hB hB1 hη hraw
  unfold IsDeviation appbLinkCountA
  rw [hchi,← hprod]
  exact ha

end WaveTurbulence.Mole

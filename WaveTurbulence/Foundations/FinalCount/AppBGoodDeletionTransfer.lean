/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBGoodNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBLinkLoss
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Conditional assembly of good literal-deletion inequalities -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Conditional assembly helper, not a source operation endpoint. The raw
count, rank identity and eventual coefficient inequality must all be proved
for the actual source operation before this lemma is applied. -/
theorem appb_good_deletion_of_raw_and_rank {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (hM : M.IsMolecule) {d : ℕ} (L γ δ C1 a γ0 C : ℝ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (q : Fin P.edges.length → (Fin d → ℤ))
    (scales : Finset V → ℝ) (rankLoss logLoss : ℕ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hC : 0 ≤ C) (hP : ∀ S,0 ≤ scales S) (hcard : 4*r.removedAtoms.card ≤ logLoss)
    (hchi : M.circuitRank = r.post.circuitRank+(rankLoss : ℤ))
    (hcoef : C*(Real.log L)^logLoss*L^(-a*γ0) ≤ L^(-5*γ0/8))
    (hraw : (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
      ENNReal.ofReal (C*L^(((d : ℝ)-γ)*(rankLoss : ℝ)-a*γ0))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞)) :
    IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
      (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
      (ENNReal.ofReal (L^(-5*γ0/8))) := by
  have hLp := zero_lt_one.trans_le hL
  have hlinks := appbLinkProduct_eraseAtoms_bound M hM r.removedAtoms L γ δ scales hLp.le hlog hδ.1.le hP
  have hpow := pow_le_pow_right₀ hlog hcard
  have hnon : 0 ≤ appbLinkProduct r.post L γ δ scales := by
    apply Finset.prod_nonneg
    intro S hS
    exact (appb_link_weight_bounds hLp.le hlog hδ.1.le (hP S) γ).1.trans' (by norm_num)
  have hlinks' : appbLinkProduct M L γ δ scales ≤ (Real.log L)^logLoss*appbLinkProduct r.post L γ δ scales :=
    hlinks.trans (mul_le_mul_of_nonneg_right hpow hnon)
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ.1 _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 :=
    (mul_le_mul ((inv_le_one₀ hCpos).mpr hC1)
      (Real.rpow_le_one hδ.1.le hδ.2 (by norm_num))
      (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have ha := appb_good_normalization_of_raw _ _ r.post.circuitRank rankLoss logLoss L ((d : ℝ)-γ)
    (C1⁻¹*δ^(1/2 : ℝ)) (appbLinkProduct M L γ δ scales) (appbLinkProduct r.post L γ δ scales)
    C a γ0 hL hB hB1 hC hlinks' hcoef hraw
  unfold IsDeviation appbLinkCountA
  rw [hchi]
  exact ha

end WaveTurbulence.Mole

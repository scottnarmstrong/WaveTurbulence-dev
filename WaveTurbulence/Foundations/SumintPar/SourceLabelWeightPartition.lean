/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLocalizationLabels
public import WaveTurbulence.Foundations.SumintPar.NormPartitionIdentity

/-!
# Exact complex weight partition over the literal source label type

The nonnegative absolute partition proves genuine summability before
complex sums are regrouped or inactive alternative labels are removed.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- The actual source label family preserves the absolute spatial weight exactly. -/
theorem tsum_sourceLabel_weight_enorm {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (x : D.S.VIdx → Fin d → ℤ) :
    (∑' j : SourceLocalizationLabel D hD, ‖localizedSourceWeight D L j.1 j.2.val E x‖ₑ) =
      ‖∏ v, D.wK v (E 0 - E 1) (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)‖ₑ := by
  exact (tsum_sourceLocalizationLabel D hD (fun a b => ‖localizedSourceWeight D L a b E x‖ₑ)).trans
    (source_weight_enorm_partition D hD E hE x).symm

/-- The actual source label weights are genuinely absolutely summable at each lattice input. -/
theorem summable_norm_sourceLabel_weight {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (x : D.S.VIdx → Fin d → ℤ) :
    Summable (fun j : SourceLocalizationLabel D hD => ‖localizedSourceWeight D L j.1 j.2.val E x‖) := by
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  rw [tsum_sourceLabel_weight_enorm D hD E hE x]
  exact enorm_ne_top

/-- The complex spatial weight partition is exact over the actual primary and alternative labels. -/
theorem tsum_sourceLabel_weight {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (x : D.S.VIdx → Fin d → ℤ) :
    (∑' j : SourceLocalizationLabel D hD, localizedSourceWeight D L j.1 j.2.val E x) =
      ∏ v, D.wK v (E 0 - E 1) (D.kVec L x E v)*D.wL v (D.ℓVec L x E v) := by
  classical
  have hs := (summable_norm_sourceLabel_weight D hD E hE x).of_norm
  have hf : Summable (fun ab : (D.S.VIdx → Fin d → ℤ) × (D.S.VIdx → Fin d → ℤ) =>
      localizedSourceWeight D L ab.1 ab.2 E x) := by
    apply Summable.of_norm
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    rw [ENNReal.tsum_prod']
    rw [source_weight_enorm_partition_full D L E x]
    exact enorm_ne_top
  calc
    _ = ∑' a : D.S.VIdx → Fin d → ℤ,
        ∑' b : {b : D.S.VIdx → Fin d → ℤ // b ∈ sourceAlternativeLabels D hD a},
          localizedSourceWeight D L a b.val E x := hs.tsum_sigma
    _ = ∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
        localizedSourceWeight D L a b E x := by
      apply tsum_congr
      intro a
      exact Finset.tsum_subtype' (sourceAlternativeLabels D hD a) (fun b => localizedSourceWeight D L a b E x)
    _ = ∑' a : D.S.VIdx → Fin d → ℤ, ∑' b : D.S.VIdx → Fin d → ℤ,
        localizedSourceWeight D L a b E x := by
      apply tsum_congr
      intro a
      exact (tsum_eq_sum (fun b hb => localizedSourceWeight_eq_zero_of_not_alternative D hD a b E hE x hb)).symm
    _ = ∑' ab : (D.S.VIdx → Fin d → ℤ) × (D.S.VIdx → Fin d → ℤ),
        localizedSourceWeight D L ab.1 ab.2 E x := hf.tsum_prod.symm
    _ = _ := by
      rw [← (Equiv.sumArrowEquivProdArrow D.S.VIdx D.S.VIdx (Fin d → ℤ)).tsum_eq]
      simpa only [localizedSourceWeight,sourceWeight,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
        Finset.prod_mul_distrib,Equiv.sumArrowEquivProdArrow_apply_fst,Equiv.sumArrowEquivProdArrow_apply_snd] using (source_weight_partition D L x E).symm

end WaveTurbulence.SumintPar

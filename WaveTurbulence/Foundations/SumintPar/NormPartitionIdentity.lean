/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.WeightPartitionIdentity
public import WaveTurbulence.Foundations.SumintPar.AlternativeLabelFamily

/-!
# Exact absolute-mass partition of the source weights

The localization profiles are nonnegative and sum to one. Consequently
the sum of the absolute localized weights is exactly the absolute
unlocalized weight, rather than merely an upper bound.
-/

@[expose] public section
set_option autoImplicit false

open Finset
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- Nonnegative localization profiles factor out of the complex norm. -/
theorem norm_localizedWeight_eq {d : ℕ} (a : Fin d → ℤ) (F : Mom d → ℂ) (x : Mom d) :
    ‖localizedWeight a F x‖ = localizationProfile a x*‖F x‖ := by
  simp only [localizedWeight,norm_smul,Real.norm_eq_abs,abs_of_nonneg (localizationProfile_nonneg a x)]

/-- A single finite cell partition preserves absolute mass exactly. -/
theorem sum_norm_localizedWeight {d : ℕ} (F : Mom d → ℂ) (x : Mom d) :
    (∑ a ∈ ApproxNT.thetaSupport ((2:ℝ) • x), ‖localizedWeight a F x‖) = ‖F x‖ := by
  simp_rw [norm_localizedWeight_eq]
  rw [← Finset.sum_mul,sum_localizationProfile,one_mul]

/-- The same one-weight identity in nonnegative extended reals. -/
theorem sum_enorm_localizedWeight {d : ℕ} (F : Mom d → ℂ) (x : Mom d) :
    (∑ a ∈ ApproxNT.thetaSupport ((2:ℝ) • x), ‖localizedWeight a F x‖ₑ) = ‖F x‖ₑ := by
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),sum_norm_localizedWeight]

/-- A finite tensor cell partition preserves the absolute weight product. -/
theorem tsum_enorm_product_localizedWeight {ι : Type*} [Fintype ι] {d : ℕ}
    (F : ι → Mom d → ℂ) (p : ι → Mom d) :
    (∑' a : ι → Fin d → ℤ, ‖∏ i, localizedWeight (a i) (F i) (p i)‖ₑ) =
      ‖∏ i, F i (p i)‖ₑ := by
  classical
  let choices := fun i => ApproxNT.thetaSupport ((2:ℝ) • p i)
  have he (a : ι → Fin d → ℤ) : ‖∏ i, localizedWeight (a i) (F i) (p i)‖ₑ =
      ∏ i, ‖localizedWeight (a i) (F i) (p i)‖ₑ := by
    simp_rw [← ofReal_norm]
    rw [norm_prod,ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  simp_rw [he]
  have hz (a : ι → Fin d → ℤ) (ha : a ∉ Fintype.piFinset choices) :
      (∏ i, ‖localizedWeight (a i) (F i) (p i)‖ₑ) = 0 := by
    have hh : ¬ ∀ i, a i ∈ choices i := fun h => ha (Fintype.mem_piFinset.mpr h)
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    apply Finset.prod_eq_zero (mem_univ i)
    rw [localizedWeight_eq_zero_of_not_active (F i) (p i) hi,enorm_zero]
  rw [tsum_eq_sum hz,← Finset.prod_univ_sum choices
    (fun i a => ‖localizedWeight a (F i) (p i)‖ₑ)]
  have hs (i : ι) : (∑ a ∈ choices i, ‖localizedWeight a (F i) (p i)‖ₑ) = ‖F i (p i)‖ₑ :=
    sum_enorm_localizedWeight (F i) (p i)
  simp_rw [hs]
  simp_rw [← ofReal_norm]
  rw [norm_prod,ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]

/-- Full primary/alternative absolute partition at each actual input. -/
theorem source_weight_enorm_partition_full {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (E : Fin 4 → Mom d) (x : D.S.VIdx → Fin d → ℤ) :
    (∑' a : D.S.VIdx → Fin d → ℤ, ∑' b : D.S.VIdx → Fin d → ℤ,
      ‖localizedSourceWeight D L a b E x‖ₑ) =
      ‖∏ v, D.wK v (E 0 - E 1) (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)‖ₑ := by
  rw [← ENNReal.tsum_prod,← (Equiv.sumArrowEquivProdArrow D.S.VIdx D.S.VIdx (Fin d → ℤ)).tsum_eq]
  have hh := tsum_enorm_product_localizedWeight (sourceWeight D (E 0 - E 1))
    (Sum.elim (D.kVec L x E) (D.ℓVec L x E))
  simpa only [localizedSourceWeight,Fintype.prod_sum_type,sourceWeight,Sum.elim_inl,Sum.elim_inr,
    Finset.prod_mul_distrib,Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.sumArrowEquivProdArrow_apply_snd] using hh

/-- Restricting alternative labels to the fixed family preserves the exact partition. -/
theorem source_weight_enorm_partition {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) (x : D.S.VIdx → Fin d → ℤ) :
    ‖∏ v, D.wK v (E 0 - E 1) (D.kVec L x E v)*D.wL v (D.ℓVec L x E v)‖ₑ =
      ∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
        ‖localizedSourceWeight D L a b E x‖ₑ := by
  rw [← source_weight_enorm_partition_full D L E x]
  apply tsum_congr
  intro a
  apply tsum_eq_sum
  intro b hb
  rw [localizedSourceWeight_eq_zero_of_not_alternative D hD a b E hE x hb,enorm_zero]

end WaveTurbulence.SumintPar

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.FiniteFactorization
public import WaveTurbulence.Foundations.Sumint.SourceWeightExpansion
import Mathlib.Tactic

/-!
# Exact partition identities before Fourier expansion

At each fixed momentum only finitely many half-mesh profiles are active.
The full weight product is therefore exactly the sum of its localized
products, without imposing additional smoothness or summability premises.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- A localized weight vanishes outside its explicit finite active label family. -/
theorem localizedWeight_eq_zero_of_not_active {d : ℕ} (F : Mom d → ℂ) (x : Mom d)
    {a : Fin d → ℤ} (ha : a ∉ ApproxNT.thetaSupport ((2 : ℝ) • x)) :
    localizedWeight a F x = 0 := by
  rw [localizedWeight, localizationProfile_eq_zero x ha, zero_smul]

/-- Exact finite partition identity for one arbitrary source weight. -/
theorem sum_localizedWeight {d : ℕ} (F : Mom d → ℂ) (x : Mom d) :
    (∑ a ∈ ApproxNT.thetaSupport ((2 : ℝ) • x), localizedWeight a F x) = F x := by
  calc
    _ = (∑ a ∈ ApproxNT.thetaSupport ((2 : ℝ) • x), localizationProfile a x) • F x := by
      rw [Finset.sum_smul]
      rfl
    _ = _ := by rw [sum_localizationProfile, one_smul]

/-- The unconditional sum is the same finite partition sum. -/
theorem tsum_localizedWeight {d : ℕ} (F : Mom d → ℂ) (x : Mom d) :
    (∑' a : Fin d → ℤ, localizedWeight a F x) = F x := by
  rw [tsum_eq_sum (s := ApproxNT.thetaSupport ((2 : ℝ) • x))
    (fun a ha => localizedWeight_eq_zero_of_not_active F x ha), sum_localizedWeight]

/-- Exact partition identity for every finite family of weights before affine composition. -/
theorem tsum_product_localizedWeight {ι : Type*} [Fintype ι] {d : ℕ}
    (F : ι → Mom d → ℂ) (p : ι → Mom d) :
    (∑' a : ι → Fin d → ℤ, ∏ i, localizedWeight (a i) (F i) (p i)) = ∏ i, F i (p i) := by
  classical
  rw [tsum_product_eq_product_tsum (fun i => ApproxNT.thetaSupport ((2 : ℝ) • p i))
    (fun i a => localizedWeight a (F i) (p i))
    (fun i _ ha => localizedWeight_eq_zero_of_not_active (F i) (p i) ha)]
  apply Finset.prod_congr rfl
  intro i _
  exact tsum_localizedWeight (F i) (p i)

/-- The literal primary/alternative source weight product is exactly its full localized expansion. -/
theorem source_weight_partition {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    (∏ v, D.wK v (D.kVec L x E v) * D.wL v (D.ℓVec L x E v)) =
      ∑' a : (D.S.VIdx ⊕ D.S.VIdx) → Fin d → ℤ,
        ∏ i, localizedWeight (a i) (sourceWeight D i)
          (Sum.elim (D.kVec L x E) (D.ℓVec L x E) i) := by
  rw [tsum_product_localizedWeight]
  simp only [sourceWeight, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_mul_distrib]

end WaveTurbulence.Sumint

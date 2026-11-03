/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NormalizedWeyl

/-! # Zero-rational Weyl moments from the single Gauss arc -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The zero-rational part is controlled by the elementary decaying profile. -/
theorem exists_zeroWeylPart_profile_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ t : ℝ,
      zeroWeylPart M t ≤ C*M*scaledArcProfile M 1 0 t := by
  obtain ⟨C,hC,hb⟩ := exists_weylSupremum_bound
  refine ⟨C^2,by positivity,?_⟩
  intro M hM t
  have hMp : 0 < M := by linarith
  by_cases ht : |t| ≤ M⁻¹
  · have hg := hb M t 0 1 hM (by norm_num) (by exact_mod_cast hM) (by norm_num)
      (by simpa only [Int.cast_zero,Nat.cast_one,zero_div,sub_zero,one_mul,one_div] using ht)
    simp only [Nat.cast_one,Int.cast_zero,zero_div,sub_zero] at hg
    have hp := rpow_le_scaledArcProfile (weylSupremum M t) (C*M) M 1 |t| 2
      (weylSupremum_nonneg hMp t) (by positivity) hMp.le (by norm_num) (abs_nonneg t) (by norm_num) hg
    have hp' : weylSupremum M t^2 ≤ (C*M)^2*scaledArcProfile M 1 0 t := by
      simpa only [Real.rpow_two,one_mul,one_pow,Real.one_rpow,div_self (by norm_num : (2 : ℝ) ≠ 0),
        mul_one,scaledArcProfile_eq,sub_zero] using hp
    change {t : ℝ | |t| ≤ 1/M}.indicator (normalizedWeyl M) t ≤ _
    rw [indicator_of_mem (show t ∈ {s : ℝ | |s| ≤ 1/M} by change |t| ≤ 1/M; simpa only [one_div] using ht),
      normalizedWeyl,div_le_iff₀ hMp]
    exact hp'.trans_eq (by ring)
  · have hz : zeroWeylPart M t = 0 := by simp [zeroWeylPart,Set.indicator,ht]
    rw [hz]
    exact mul_nonneg (mul_nonneg (sq_nonneg C) hMp.le) (scaledArcProfile_nonneg _ _ _ _)

/-- Raising the order-one profile raises its decay exponent. -/
theorem scaledArcProfile_one_rpow {M t : ℝ} (ℓ : ℝ) :
    scaledArcProfile M 1 0 t^ℓ = scaledArcProfile M ℓ 0 t := by
  dsimp [scaledArcProfile,arcProfile]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1+|M^2*(t-0)|)]
  congr 1
  ring

/-- Every zero-arc moment of order greater than one has the sharp mass
`M^(ℓ-2)`. Lower moments on finite windows follow by Hölder. -/
theorem exists_zeroWeylPart_moment_bound (ℓ : ℝ) (hℓ : 1 < ℓ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      Integrable (fun t => zeroWeylPart M t^ℓ) ∧
      (∫ t, zeroWeylPart M t^ℓ) ≤ C*M^(ℓ-2) := by
  obtain ⟨C,hC,hpoint⟩ := exists_zeroWeylPart_profile_bound
  let K := C^ℓ*arcProfileMass ℓ
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hC.le _) (arcProfileMass_nonneg _)
  refine ⟨K+1,by positivity,?_⟩
  intro M hM
  have hMp : 0 < M := by linarith
  have hmajor (t : ℝ) : zeroWeylPart M t^ℓ ≤ C^ℓ*M^ℓ*scaledArcProfile M ℓ 0 t := by
    have hh := Real.rpow_le_rpow (zeroWeylPart_nonneg hMp t) (hpoint M hM t) (by linarith : 0 ≤ ℓ)
    rw [Real.mul_rpow (mul_nonneg hC.le hMp.le) (scaledArcProfile_nonneg _ _ _ _),
      Real.mul_rpow hC.le hMp.le,scaledArcProfile_one_rpow] at hh
    exact hh
  have hmajori : Integrable (fun t => C^ℓ*M^ℓ*scaledArcProfile M ℓ 0 t) :=
    (integrable_scaledArcProfile hMp hℓ 0).const_mul _
  have hi : Integrable (fun t => zeroWeylPart M t^ℓ) := by
    apply hmajori.mono' ((measurable_zeroWeylPart hMp).pow_const ℓ).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _)]
    exact hmajor t
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, C^ℓ*M^ℓ*scaledArcProfile M ℓ 0 t := integral_mono_ae hi hmajori (Filter.Eventually.of_forall hmajor)
    _ = K*M^(ℓ-2) := by
      rw [integral_const_mul,integral_scaledArcProfile hMp,Real.rpow_sub hMp,Real.rpow_two]
      dsimp [K]
      ring
    _ ≤ (K+1)*M^(ℓ-2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end WaveTurbulence.WeylSums

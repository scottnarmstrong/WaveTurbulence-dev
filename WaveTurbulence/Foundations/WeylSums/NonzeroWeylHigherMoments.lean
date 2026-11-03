/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylMoments

/-! # Higher nonzero-arc moments from the uniform cap -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- Above order `2+ε`, the cap costs only the expected scale power. -/
theorem exists_nonzeroWeylPart_higher_moment_bound (ε b : ℝ) (hε : 0 < ε)
    (hba : 2+ε ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T : ℝ, 2 ≤ M → 0 < T → T ≤ 1 →
      IntegrableOn (fun t => nonzeroWeylPart M t^b) {t : ℝ | |t| ≤ T} ∧
      (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^b) ≤ C*M^(b-2)*T := by
  let a := 2+ε
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := ha.trans_le hba
  obtain ⟨C,hC,hbound⟩ := exists_nonzeroWeylPart_moment_bound a (ε/2)
    (by dsimp [a]; linarith) (by positivity) (by dsimp [a]; linarith)
  let K := C*(25 : ℝ)^(b-a)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro M T hM hT hT1
  have hMp : 0 < M := by linarith
  obtain ⟨hi,hbnd⟩ := hbound M T hM hT
  have hpoint (t : ℝ) : nonzeroWeylPart M t^b ≤ (25*M)^(b-a)*nonzeroWeylPart M t^a := by
    have hn := nonzeroWeylPart_nonneg hMp t
    by_cases hz : nonzeroWeylPart M t = 0
    · simp [hz,Real.zero_rpow hb.ne',Real.zero_rpow ha.ne']
    · have hp : 0 < nonzeroWeylPart M t := lt_of_le_of_ne hn (Ne.symm hz)
      calc
        _ = nonzeroWeylPart M t^(b-a)*nonzeroWeylPart M t^a := by
          rw [← Real.rpow_add hp]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hn (nonzeroWeylPart_le (by linarith) t) (sub_nonneg.mpr hba)) (by positivity)
  have hib : IntegrableOn (fun t => nonzeroWeylPart M t^b) {t : ℝ | |t| ≤ T} := by
    apply (hi.const_mul ((25*M)^(b-a))).mono' ((measurable_nonzeroWeylPart hMp).pow_const b).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (nonzeroWeylPart_nonneg hMp t) _)]
    exact hpoint t
  refine ⟨hib,?_⟩
  have hTpow : T^(a-1-ε/2) ≤ T := Real.rpow_le_self_of_le_one hT.le hT1 (by dsimp [a]; linarith)
  calc
    _ ≤ ∫ t in {t : ℝ | |t| ≤ T}, (25*M)^(b-a)*nonzeroWeylPart M t^a :=
      integral_mono_ae hib (hi.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = (25*M)^(b-a)*(∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a) := integral_const_mul _ _
    _ ≤ (25*M)^(b-a)*(C*M^(a-2)*T^(a-1-ε/2)) := mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ ≤ (25*M)^(b-a)*(C*M^(a-2)*T) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hTpow (by positivity)) (by positivity)
    _ = K*M^(b-2)*T := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 25) hMp.le]
      calc
        _ = (C*(25 : ℝ)^(b-a))*(M^(b-a)*M^(a-2))*T := by ring
        _ = _ := by
          rw [← Real.rpow_add hMp,show b-a+(a-2) = b-2 by ring]

end WaveTurbulence.WeylSums

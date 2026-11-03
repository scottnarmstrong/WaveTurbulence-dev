/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylLowerMoments
public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylHigherMoments

/-! # Half-dimension nonzero-arc moments -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- A common bound in dimension four and above. The small extra scale loss
allows one uniform expression across the critical moment threshold. -/
theorem exists_nonzeroWeylPart_half_moment_bound (d : ℕ) (hd : 4 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T : ℝ, 2 ≤ M → 0 < T → T ≤ 1 →
      IntegrableOn (fun t => nonzeroWeylPart M t^((d : ℝ)/2)) {t : ℝ | |t| ≤ T} ∧
      (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^((d : ℝ)/2)) ≤
        C*M^((d : ℝ)/2-2+ε)*T := by
  by_cases hd4 : d = 4
  · subst d
    obtain ⟨C,hC,hb⟩ := exists_nonzeroWeylPart_lower_moment_bound ε 2 hε (by norm_num) (by linarith)
    refine ⟨C,hC,?_⟩
    intro M T hM hT hT1
    simpa only [Nat.cast_ofNat,show (4 : ℝ)/2 = 2 by norm_num,sub_self,zero_add] using hb M T hM hT hT1
  · have hd5 : 5 ≤ d := by omega
    have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd5
    obtain ⟨C,hC,hb⟩ := exists_nonzeroWeylPart_higher_moment_bound ε ((d : ℝ)/2) hε (by linarith)
    refine ⟨C,hC,?_⟩
    intro M T hM hT hT1
    obtain ⟨hi,hh⟩ := hb M T hM hT hT1
    refine ⟨hi,hh.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hT.le
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end WaveTurbulence.WeylSums

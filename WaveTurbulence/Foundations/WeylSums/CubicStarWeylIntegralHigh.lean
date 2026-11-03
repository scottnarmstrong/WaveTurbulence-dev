/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarMinIntegral
public import WaveTurbulence.Foundations.WeylSums.NonzeroWeylHalfMoment
public import WaveTurbulence.Foundations.WeylSums.ZeroWeylMoments

/-! # The shared-vertex Weyl minimum in dimension four and above -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- In higher dimension both product moments are bounded by the same
power, and the two-time window retains one full factor `T`. -/
theorem exists_cubicStar_weyl_integral_bound_high (d : ℕ) (hd : 4 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ M A T : ℝ, 2 ≤ M → 1/M < A → 0 < T → T ≤ 1 →
      IntegrableOn (fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^d) (normalizedWeyl M xy.2^d))
        (timeSquareWindow A T) ∧
      (∫ xy : ℝ × ℝ in timeSquareWindow A T,
        min (normalizedWeyl M xy.1^d) (normalizedWeyl M xy.2^d)) ≤
        C*M^((d : ℝ)-4+2*ε)*T := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  let a := 2+ε
  let k := (d : ℝ)-a
  have hk : 1 < k := by dsimp [k,a]; linarith
  obtain ⟨C₁,hC₁,hb₁⟩ := exists_nonzeroWeylPart_half_moment_bound d hd ε hε hεsmall
  obtain ⟨C₂,hC₂,hb₂⟩ := exists_nonzeroWeylPart_higher_moment_bound ε a hε le_rfl
  obtain ⟨C₃,hC₃,hb₃⟩ := exists_zeroWeylPart_moment_bound k hk
  let C := 2*C₁^2+2*C₂*C₃
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M A T hM hA hT hT1
  have hMp : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨hi₁,h₁⟩ := hb₁ M T hM hT hT1
  obtain ⟨hi₂,h₂⟩ := hb₂ M T hM hT hT1
  obtain ⟨hi₃,h₃⟩ := hb₃ M hM1
  have hZ : (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^k) ≤ C₃*M^(k-2) :=
    (setIntegral_le_integral hi₃ (Filter.Eventually.of_forall
      (fun t => Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _))).trans h₃
  obtain ⟨hi,hb⟩ := integral_normalizedWeyl_min_le_moments d (by omega) M A T a hMp hA
    (by dsimp [a]; linarith) (by dsimp [a]; linarith) hi₁ hi₂ hi₃.restrict
  refine ⟨hi,?_⟩
  have hNN : (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^((d : ℝ)/2))^2 ≤
      C₁^2*M^((d : ℝ)-4+2*ε)*T := by
    have hs := (sq_le_sq₀ (integral_nonneg (fun t => Real.rpow_nonneg (nonzeroWeylPart_nonneg hMp t) _))
      (by positivity : 0 ≤ C₁*M^((d : ℝ)/2-2+ε)*T)).mpr h₁
    have halg : (C₁*M^((d : ℝ)/2-2+ε)*T)^2 = C₁^2*M^((d : ℝ)-4+2*ε)*T^2 := by
      rw [mul_pow,mul_pow,← Real.rpow_two (M^((d : ℝ)/2-2+ε)),← Real.rpow_mul hMp.le]
      rw [show ((d : ℝ)/2-2+ε)*2 = (d : ℝ)-4+2*ε by ring]
    rw [halg] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hT,hT1] : T^2 ≤ T) (by positivity))
  have hNZ : (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a)*
      (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^k) ≤
      C₂*C₃*M^((d : ℝ)-4+2*ε)*T := by
    have hh := mul_le_mul h₂ hZ (integral_nonneg (fun t => Real.rpow_nonneg (zeroWeylPart_nonneg hMp t) _)) (by positivity)
    have halg : (C₂*M^(a-2)*T)*(C₃*M^(k-2)) = C₂*C₃*M^((d : ℝ)-4)*T := by
      calc
        _ = (C₂*C₃)*(M^(a-2)*M^(k-2))*T := by ring
        _ = _ := by
          rw [← Real.rpow_add hMp,show a-2+(k-2) = (d : ℝ)-4 by dsimp [k]; ring]
    rw [halg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)) (by positivity)) hT.le)
  calc
    _ ≤ 2*(C₁^2*M^((d : ℝ)-4+2*ε)*T)+2*(C₂*C₃*M^((d : ℝ)-4+2*ε)*T) := by
      linarith only [hb,hNN,hNZ]
    _ = C*M^((d : ℝ)-4+2*ε)*T := by dsimp [C]; ring

end WaveTurbulence.WeylSums
